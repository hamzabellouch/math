import OAI.Analysis.Cuntz.Distribution

namespace OAI

noncomputable section

/-! Order of spectral cutoffs, translations, and continuity. -/

open scoped Matrix CStarAlgebra NNReal
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus productMatrixRealFunctionalCalculus
variable {A : Type*} [CStarAlgebra A]

/-- One-sided order perturbation suffices for strict cutoff comparison. -/
theorem cuntzLE_cutoff_of_le_add {n : ℕ}
    {a b : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a)
    {δ ε : ℝ} (hδε : δ < ε) (hab : a ≤ b + δ • 1) :
    CuntzLE (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε))
      (CStarMatrix.ofMatrix.symm b) := by
  have hδ : 0 < ε-δ := sub_pos.mpr hδε
  obtain ⟨x, hx, hsq, hloc⟩ := exists_cutoff_localizer ha ε
  have hc := star_left_conjugate_le_conjugate hab x
  simp only [hx, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hsq] at hc
  have hbound : (ε-δ) • cuntzCutoff a ε ≤ x*b*x := by
    rw [sub_smul]
    exact sub_le_iff_le_add.mpr (hloc.trans hc)
  have hcmp := cuntzLE_of_nonneg_le (smul_nonneg hδ.le (cuntzCutoff_nonneg a ε)) hbound
  have hsc := cuntzEquivalent_pos_smul (cuntzCutoff a ε) hδ
  have hex := CuntzLE.exact (CStarMatrix.ofMatrix.symm b) (CStarMatrix.ofMatrix.symm x)
  change CuntzLE (CStarMatrix.ofMatrix.symm (x*b*star x)) _ at hex
  rw [hx] at hex
  exact hsc.2.trans (hcmp.trans hex)

/-- The positive part plus the threshold dominates the original element. -/
theorem le_cuntzCutoff_add {a : A} (ha : 0 ≤ a) (t : ℝ) :
    a ≤ cuntzCutoff a t + t • 1 := by
  have h := cfc_mono (a := a) (f := fun s : ℝ => s)
    (g := fun s : ℝ => max (s-t) 0 + t) (fun s _ => by linarith [le_max_left (s-t) 0])
  rw [cfc_add (a := a) (fun s : ℝ => max (s-t) 0) (fun _ => t)] at h
  simpa only [cfc_const t a ha.isSelfAdjoint, cfc_id' ℝ a ha.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one, cuntzCutoff] using h

/-- Positive order preserves matching cutoff Cuntz classes.
This is Cuntz comparison, not operator monotonicity of positive parts. -/
theorem cuntzLE_cutoff_of_le {n : ℕ} {a b : CStarMatrix (Fin n) (Fin n) A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (t : ℝ) :
    CuntzLE (CStarMatrix.ofMatrix.symm (cuntzCutoff a t))
      (CStarMatrix.ofMatrix.symm (cuntzCutoff b t)) := by
  apply (cuntzLE_iff_all_cutoffs _ (cuntzCutoff_nonneg a t) _).mpr
  intro δ hδ
  rw [cuntzCutoff_cutoff ha t hδ.le]
  exact cuntzLE_cutoff_of_le_add ha (by linarith : t < t+δ)
    (hab.trans (le_cuntzCutoff_add hb t))

namespace CuntzDimensionState

theorem distribution_mono_positive (d : CuntzDimensionState A) {n : ℕ}
    {a b : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≤ b) (t : ℝ) :
    d.distribution ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ t ≤
      d.distribution ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ t :=
  d.regularized_mono (cuntzLE_cutoff_of_le ha hb hab t)

/-- The actual layer-cake integral is monotone on each positive matrix cone. -/
theorem spectralValue_mono_positive (d : CuntzDimensionState A) {n : ℕ}
    {a b : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ ≤
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  let pa : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩
  let pb : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩
  have hR : ‖a‖ ≤ ‖a‖ + ‖b‖ := le_add_of_nonneg_right (norm_nonneg b)
  have hR' : ‖b‖ ≤ ‖a‖ + ‖b‖ := le_add_of_nonneg_left (norm_nonneg a)
  rw [d.spectralValue_eq_integral pa hR, d.spectralValue_eq_integral pb hR']
  exact intervalIntegral.integral_mono_on (add_nonneg (norm_nonneg a) (norm_nonneg b))
    (d.distribution_intervalIntegrable pa _ _) (d.distribution_intervalIntegrable pb _ _)
    (fun t _ => d.distribution_mono_positive ha hb hab t)

end CuntzDimensionState

theorem cuntzCutoff_add_scalar {a : A} (ha : 0 ≤ a) (r t : ℝ) :
    cuntzCutoff (a + r • 1) t = cuntzCutoff a (t-r) := by
  have he : cfc (fun s : ℝ => s+r) a = a+r • 1 := by
    rw [cfc_add (a := a) (fun s : ℝ => s) (fun _ => r), cfc_id' ℝ a ha.isSelfAdjoint, cfc_const r a ha.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
  unfold cuntzCutoff
  rw [← he, ← cfc_comp' (fun s : ℝ => max (s-t) 0) (fun s : ℝ => s+r) a]
  apply cfc_congr
  intro s hs
  dsimp only
  congr 1
  ring

/-- A negative spectral threshold contributes at least its opposite scalar. -/
theorem neg_smul_one_le_cuntzCutoff {a : A} (ha : 0 ≤ a) (t : ℝ) :
    (-t) • (1 : A) ≤ cuntzCutoff a t := by
  have he : cfc (fun _ : ℝ => -t) a ≤ cfc (fun s : ℝ => max (s-t) 0) a := by
    apply cfc_mono (hf := continuousOn_const) (hg := by fun_prop)
    intro s hs
    have hs0 := spectrum_nonneg_of_nonneg ha hs
    exact (by linarith : -t ≤ s-t).trans (le_max_left _ _)
  simpa only [cfc_const (-t) a ha.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one, cuntzCutoff] using he

/-- Adding a nonnegative scalar identity to an actual positive finite matrix. -/
def CuntzPositiveMatrix.shift (a : CuntzPositiveMatrix A) (r : ℝ) (hr : 0 ≤ r) :
    CuntzPositiveMatrix A :=
  ⟨a.size, CStarMatrix.ofMatrix.symm (CStarMatrix.ofMatrix a.matrix + r • 1),
    add_nonneg a.nonneg (smul_nonneg hr zero_le_one)⟩

namespace CuntzDimensionState

theorem distribution_shift (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    (r : ℝ) (hr : 0 ≤ r) (t : ℝ) :
    d.distribution (a.shift r hr) t = d.distribution a (t-r) := by
  unfold distribution
  have he : (a.shift r hr).cutoff t = a.cutoff (t-r) := by
    cases a with
    | mk n a ha =>
      have hc := cuntzCutoff_add_scalar ha r t
      change CuntzPositiveMatrix.mk n
        (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a + r • 1) t)) _ =
        CuntzPositiveMatrix.mk n
          (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a) (t-r))) _
      congr 1
  rw [he]

/-- Below zero, every positive matrix has full normalized spectral dimension. -/
theorem distribution_of_neg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {t : ℝ} (ht : t < 0) : d.distribution a t = (a.size : ℝ) := by
  apply le_antisymm (d.distribution_le_size a t)
  have hle := neg_smul_one_le_cuntzCutoff a.nonneg t
  let p : CuntzPositiveMatrix A := ⟨a.size,
    CStarMatrix.ofMatrix.symm ((-t) • (1 : CStarMatrix (Fin a.size) (Fin a.size) A)),
    smul_nonneg (neg_pos.mpr ht).le zero_le_one⟩
  have hp : d.regularized p = (a.size : ℝ) := by
    rw [← d.regularized_unit a.size]
    exact d.regularized_eq (cuntzEquivalent_pos_smul 1 (neg_pos.mpr ht))
  rw [← hp]
  exact d.regularized_mono (cuntzLE_of_nonneg_le p.nonneg hle)

/-- Translation by a nonnegative scalar identity adds exactly size times scalar. -/
theorem spectralValue_shift (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    (r : ℝ) (hr : 0 ≤ r) :
    d.spectralValue (a.shift r hr) = d.spectralValue a + r * a.size := by
  let : NormedSpace ℝ (CStarMatrix (Fin a.size) (Fin a.size) A) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let : NormSMulClass ℝ (CStarMatrix (Fin a.size) (Fin a.size) A) :=
    NormedSpace.toNormSMulClass
  let R := ‖CStarMatrix.ofMatrix a.matrix‖ + r
  have hR : ‖CStarMatrix.ofMatrix (a.shift r hr).matrix‖ ≤ R := by
    change ‖CStarMatrix.ofMatrix a.matrix + r • 1‖ ≤ ‖CStarMatrix.ofMatrix a.matrix‖ + r
    apply (norm_add_le _ _).trans
    apply add_le_add_right
    rw [norm_smul, Real.norm_of_nonneg hr]
    have h1 : ‖(1 : CStarMatrix (Fin a.size) (Fin a.size) A)‖ ≤ 1 := by
      nontriviality CStarMatrix (Fin a.size) (Fin a.size) A
      simp only [norm_one, le_refl]
    exact mul_le_of_le_one_right hr h1
  rw [d.spectralValue_eq_integral _ hR]
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (d.distribution_intervalIntegrable (a.shift r hr) 0 r)
    (d.distribution_intervalIntegrable (a.shift r hr) r R)
  rw [← hi]
  have hlow : (∫ t in (0 : ℝ)..r, d.distribution (a.shift r hr) t) = r*a.size := by
    have he := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hr
      (f := d.distribution (a.shift r hr)) (g := fun _ => (a.size : ℝ)) (by
        intro t ht
        rw [d.distribution_shift]
        exact d.distribution_of_neg a (sub_neg.mpr ht.2))
    simpa using he
  rw [hlow]
  simp_rw [d.distribution_shift]
  rw [intervalIntegral.integral_comp_sub_right]
  simp only [sub_self, R, add_sub_cancel_right, spectralValue]
  exact add_comm _ _


/-- One-sided norm control for the actual spectral integral. -/
theorem spectralValue_le_add_norm (d : CuntzDimensionState A) {n : ℕ}
    {a b : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ ≤
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ + ‖a-b‖ * n := by
  have hab : a ≤ b + ‖a-b‖ • 1 := by
    have he := (ha.isSelfAdjoint.sub hb.isSelfAdjoint).le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at he
    exact sub_le_iff_le_add'.mp he
  let pb : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩
  have h := d.spectralValue_mono_positive ha (pb.shift ‖a-b‖ (norm_nonneg _)).nonneg hab
  change d.spectralValue _ ≤ d.spectralValue (pb.shift ‖a-b‖ (norm_nonneg _)) at h
  rwa [d.spectralValue_shift] at h

/-- On n-by-n positives the integral is n-Lipschitz in the actual C*-norm. -/
theorem abs_spectralValue_sub_le (d : CuntzDimensionState A) {n : ℕ}
    {a b : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ -
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩| ≤ ‖a-b‖ * n := by
  have h := d.spectralValue_le_add_norm ha hb
  have h' := d.spectralValue_le_add_norm hb ha
  rw [norm_sub_rev b a] at h'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem spectralValue_lipschitz (d : CuntzDimensionState A) (n : ℕ) :
    LipschitzWith (n : ℝ≥0) (fun a : {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} =>
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a.val, a.property⟩) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [Real.dist_eq, Subtype.dist_eq, dist_eq_norm, NNReal.coe_natCast, Real.norm_eq_abs, mul_comm]
    using d.abs_spectralValue_sub_le a.property b.property

/-- Continuity on the full positive cone, without a finite-spectrum assumption. -/
theorem spectralValue_continuous (d : CuntzDimensionState A) (n : ℕ) :
    Continuous (fun a : {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} =>
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a.val, a.property⟩) :=
  (d.spectralValue_lipschitz n).continuous

end CuntzDimensionState
end Kaplansky

end

end OAI
