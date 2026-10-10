import OAI.Analysis.Cuntz.RegularizedState
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

noncomputable section

/-! Spectral distributions, integrals, and scalar covariance. -/

open scoped Matrix CStarAlgebra
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- A positive cutoff vanishes above the actual spectral norm bound. -/
theorem cuntzCutoff_eq_zero_of_norm_le {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : ‖a‖ ≤ ε) :
    cuntzCutoff a ε = 0 := by
  nontriviality A
  change cfc (fun t : ℝ => max (t-ε) 0) a = 0
  rw [← cfc_zero ℝ a]
  apply cfc_congr
  intro t ht
  have h : t ≤ ε := by
    simpa only [Real.norm_of_nonneg (spectrum_nonneg_of_nonneg ha ht)] using
      (spectrum.norm_le_norm_of_mem ht).trans hε
  exact max_eq_right (sub_nonpos.mpr h)

theorem cuntzCutoff_one_of_lt {t : ℝ} (ht : t < 1) :
    cuntzCutoff (1 : A) t = (1 - t) • (1 : A) := by
  have h := cfc_algebraMap (A := A) (1 : ℝ) (fun x : ℝ => max (x - t) 0)
  simpa only [cuntzCutoff, map_one, max_eq_left (sub_nonneg.mpr ht.le),
    Algebra.algebraMap_eq_smul_one] using h

namespace CuntzDimensionState

theorem regularized_of_matrix_eq_zero (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    (ha : a.matrix = 0) : d.regularized a = 0 := by
  rw [← d.regularized_zero]
  apply d.regularized_eq
  change CuntzEquivalent a.matrix (0 : Matrix (Fin 0) (Fin 0) A)
  rw [ha]
  exact ⟨CuntzLE.zero _, CuntzLE.zero _⟩

/-- The regularized spectral distribution attached to an actual positive matrix. -/
def distribution (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) (t : ℝ) : ℝ :=
  d.regularized (a.cutoff t)

theorem distribution_antitone (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    Antitone (d.distribution a) := by
  intro s t h
  exact d.regularized_mono (a := a.cutoff t) (b := a.cutoff s)
    (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg _ _) (cuntzCutoff_antitone _ h))

theorem distribution_nonneg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) (t : ℝ) :
    0 ≤ d.distribution a t := d.regularized_nonneg _

theorem distribution_le_size (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) (t : ℝ) :
    d.distribution a t ≤ a.size := d.regularized_le_size _

theorem distribution_eq_zero (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {t : ℝ} (ht : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ t) : d.distribution a t = 0 := by
  apply d.regularized_of_matrix_eq_zero
  change CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a.matrix) t) = 0
  rw [cuntzCutoff_eq_zero_of_norm_le a.nonneg ht]
  rfl

theorem distribution_intervalIntegrable (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    (s t : ℝ) : IntervalIntegrable (d.distribution a) volume s t :=
  (d.distribution_antitone a).intervalIntegrable

theorem distribution_add (d : CuntzDimensionState A) (a b : CuntzPositiveMatrix A) (t : ℝ) :
    d.distribution (a.add b) t = d.distribution a t + d.distribution b t := by
  simp only [distribution, CuntzPositiveMatrix.cutoff_add, d.regularized_add]

/-- Finite layer-cake integral. This definition does not assert the quasitrace axioms. -/
def spectralValue (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) : ℝ :=
  ∫ t in (0 : ℝ)..‖CStarMatrix.ofMatrix a.matrix‖, d.distribution a t

theorem spectralValue_nonneg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    0 ≤ d.spectralValue a :=
  intervalIntegral.integral_nonneg_of_forall (norm_nonneg _) (d.distribution_nonneg a)

theorem spectralValue_le_norm_mul_size (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.spectralValue a ≤ ‖CStarMatrix.ofMatrix a.matrix‖ * a.size := by
  have h := intervalIntegral.integral_mono_on (norm_nonneg (CStarMatrix.ofMatrix a.matrix))
    (d.distribution_intervalIntegrable a 0 _) intervalIntegrable_const
    (fun t _ => d.distribution_le_size a t)
  simpa only [spectralValue, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h


/-- The layer-cake integral is independent of an upper endpoint past the norm. -/
theorem spectralValue_eq_integral (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {R : ℝ} (hR : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ R) :
    d.spectralValue a = ∫ t in (0 : ℝ)..R, d.distribution a t := by
  have he : (∫ t in ‖CStarMatrix.ofMatrix a.matrix‖..R, d.distribution a t) = 0 := by
    have h := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hR
      (g := fun _ : ℝ => (0 : ℝ)) (fun t ht => d.distribution_eq_zero a ht.1.le)
    simpa using h
  have h := intervalIntegral.integral_add_adjacent_intervals
    (d.distribution_intervalIntegrable a 0 ‖CStarMatrix.ofMatrix a.matrix‖)
    (d.distribution_intervalIntegrable a ‖CStarMatrix.ofMatrix a.matrix‖ R)
  rw [he, add_zero] at h
  exact h

/-- Block addition is preserved by the finite spectral integral. -/
theorem spectralValue_add (d : CuntzDimensionState A) (a b : CuntzPositiveMatrix A) :
    d.spectralValue (a.add b) = d.spectralValue a + d.spectralValue b := by
  let R := ‖CStarMatrix.ofMatrix (a.add b).matrix‖ +
    ‖CStarMatrix.ofMatrix a.matrix‖ + ‖CStarMatrix.ofMatrix b.matrix‖
  have ha : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ R := by
    dsimp [R]
    linarith [norm_nonneg (CStarMatrix.ofMatrix (a.add b).matrix),
      norm_nonneg (CStarMatrix.ofMatrix a.matrix), norm_nonneg (CStarMatrix.ofMatrix b.matrix)]
  have hb : ‖CStarMatrix.ofMatrix b.matrix‖ ≤ R := by
    dsimp [R]
    linarith [norm_nonneg (CStarMatrix.ofMatrix (a.add b).matrix),
      norm_nonneg (CStarMatrix.ofMatrix a.matrix), norm_nonneg (CStarMatrix.ofMatrix b.matrix)]
  have hab : ‖CStarMatrix.ofMatrix (a.add b).matrix‖ ≤ R := by
    dsimp [R]
    linarith [norm_nonneg (CStarMatrix.ofMatrix (a.add b).matrix),
      norm_nonneg (CStarMatrix.ofMatrix a.matrix), norm_nonneg (CStarMatrix.ofMatrix b.matrix)]
  rw [d.spectralValue_eq_integral _ hab, d.spectralValue_eq_integral _ ha,
    d.spectralValue_eq_integral _ hb]
  simp_rw [d.distribution_add]
  exact intervalIntegral.integral_add (d.distribution_intervalIntegrable a 0 R)
    (d.distribution_intervalIntegrable b 0 R)

/-- A normalized dimension state forces the underlying algebra to be nonzero. -/
theorem nontrivial (d : CuntzDimensionState A) : Nontrivial A := by
  rcases subsingleton_or_nontrivial A with h | h
  · let := h
    have he := d.regularized_of_matrix_eq_zero (.unit 1) (Subsingleton.elim _ _)
    rw [d.regularized_unit] at he
    norm_num at he
  · exact h

theorem distribution_unit_of_lt (d : CuntzDimensionState A) (n : ℕ) {t : ℝ} (ht : t < 1) :
    d.distribution (.unit n) t = (n : ℝ) := by
  have hp : 0 < 1-t := sub_pos.mpr ht
  have he := cuntzCutoff_one_of_lt (A := CStarMatrix (Fin n) (Fin n) A) ht
  rw [← d.regularized_unit n]
  apply d.regularized_eq
  change CuntzEquivalent (CStarMatrix.ofMatrix.symm
    (cuntzCutoff (1 : CStarMatrix (Fin n) (Fin n) A) t)) (1 : Matrix (Fin n) (Fin n) A)
  rw [he]
  exact cuntzEquivalent_pos_smul 1 hp

/-- The finite spectral integral has exactly the required matrix-unit values. -/
theorem spectralValue_unit (d : CuntzDimensionState A) (n : ℕ) :
    d.spectralValue (.unit n) = (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    have h := d.spectralValue_le_norm_mul_size (.unit 0)
    have hp := d.spectralValue_nonneg (.unit 0)
    change d.spectralValue (.unit 0) ≤ ‖CStarMatrix.ofMatrix (CuntzPositiveMatrix.unit (A := A) 0).matrix‖ * ((0 : ℕ) : ℝ) at h
    rw [Nat.cast_zero, mul_zero] at h
    simpa only [Nat.cast_zero] using le_antisymm h hp
  · let := d.nontrivial
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    change (∫ t in (0 : ℝ)..‖(1 : CStarMatrix (Fin n) (Fin n) A)‖,
      d.distribution (.unit n) t) = _
    rw [norm_one]
    have he := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (f := d.distribution (.unit n)) (g := fun _ : ℝ => (n : ℝ))
      (fun t ht => d.distribution_unit_of_lt n ht.2)
    simpa using he

end CuntzDimensionState

/-- Scaling the element rescales the spectral threshold. -/
theorem cuntzCutoff_pos_smul {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    cuntzCutoff (r • a) t = r • cuntzCutoff a (t/r) := by
  unfold cuntzCutoff
  rw [← cfc_comp_const_mul r (fun s : ℝ => max (s-t) 0) a (ha := ha.isSelfAdjoint),
    ← cfc_const_mul r (fun s : ℝ => max (s-t/r) 0) a]
  apply cfc_congr
  intro s hs
  dsimp only
  rw [mul_max_of_nonneg _ _ hr.le, mul_zero, mul_sub, mul_div_cancel₀ _ hr.ne']

/-- Nonnegative scalar multiplication of a positive finite matrix. -/
def CuntzPositiveMatrix.scale (a : CuntzPositiveMatrix A) (r : ℝ) (hr : 0 ≤ r) :
    CuntzPositiveMatrix A :=
  ⟨a.size, CStarMatrix.ofMatrix.symm (r • CStarMatrix.ofMatrix a.matrix),
    smul_nonneg hr a.nonneg⟩

namespace CuntzDimensionState

theorem distribution_pos_scale (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    d.distribution (a.scale r hr.le) t = d.distribution a (t/r) := by
  apply d.regularized_eq
  have he := cuntzCutoff_pos_smul a.nonneg hr t
  have hc := cuntzEquivalent_pos_smul
    (cuntzCutoff (CStarMatrix.ofMatrix a.matrix) (t / r)) hr
  exact Eq.mpr (congrArg (fun c => CuntzEquivalent (CStarMatrix.ofMatrix.symm c)
    (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a.matrix) (t / r)))) he) hc

/-- The integral scales with the positive scalar, including zero. -/
theorem spectralValue_scale (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    (r : ℝ) (hr : 0 ≤ r) :
    d.spectralValue (a.scale r hr) = r * d.spectralValue a := by
  rcases eq_or_lt_of_le hr with h | h
  · subst r
    have hn : ‖CStarMatrix.ofMatrix (a.scale 0 hr).matrix‖ = 0 := by
      change ‖(0 : ℝ) • CStarMatrix.ofMatrix a.matrix‖ = 0
      rw [zero_smul, norm_zero]
    simp only [spectralValue, hn, intervalIntegral.integral_same, zero_mul]
  · let : NormedSpace ℝ (CStarMatrix (Fin a.size) (Fin a.size) A) :=
      NormedSpace.restrictScalars ℝ ℂ _
    let : NormSMulClass ℝ (CStarMatrix (Fin a.size) (Fin a.size) A) :=
      NormedSpace.toNormSMulClass
    change (∫ t in (0 : ℝ)..‖r • CStarMatrix.ofMatrix a.matrix‖,
        d.distribution (a.scale r hr) t) = _
    simp_rw [d.distribution_pos_scale a h]
    rw [norm_smul, Real.norm_of_nonneg hr, intervalIntegral.integral_comp_div _ h.ne']
    simp only [zero_div, mul_div_cancel_left₀ _ h.ne', smul_eq_mul, spectralValue]

end CuntzDimensionState
end Kaplansky

end

end OAI
