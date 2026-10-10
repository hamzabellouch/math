import OAI.NumberTheory.TotientAsymptotic.RegionLower
import OAI.NumberTheory.TotientAsymptotic.SimplexShell

namespace OAI

/-! Relating our terminal coefficient to Ford's stronger terminal inequality. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma a_one_lt_one : a 1 < 1 := by
  norm_num [a]
  linarith [Real.log_two_lt_d9]

lemma prefixRegion_nonneg {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) : ∀ i, 0 ≤ u i := by
  have hh := prefixLinear_terminal_lower u 0 (fun i => by simpa using hu.1 i)
  simpa using hh

def fordSimplex (N : ℕ) (B : ℝ) : Set (Fin (N+2) → ℝ) :=
  prefixRegion (N+2) B 0 0 ∩
    {u | u (Fin.last (N+1)) ≤ u ⟨N, by omega⟩}

def shrinkLast (N : ℕ) : (Fin (N+2) → ℝ) →ₗ[ℝ] (Fin (N+2) → ℝ) :=
  Matrix.toLin' (Matrix.diagonal (fun i => if i = Fin.last (N+1) then a 1 else 1))

lemma shrinkLast_apply (N : ℕ) (u : Fin (N+2) → ℝ) (i : Fin (N+2)) :
    shrinkLast N u i = (if i = Fin.last (N+1) then a 1 else 1)*u i := by
  simp [shrinkLast, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma shrinkLast_det (N : ℕ) : LinearMap.det (shrinkLast N) = a 1 := by
  rw [shrinkLast, LinearMap.det_toLin', Matrix.det_diagonal]
  simp

lemma shrinkLast_le {N : ℕ} {u : Fin (N+2) → ℝ} (hu : ∀ i, 0 ≤ u i) :
    ∀ i, shrinkLast N u i ≤ u i := by
  intro i
  rw [shrinkLast_apply]
  split_ifs
  · exact mul_le_of_le_one_left (hu i) a_one_lt_one.le
  · simp

/-- Scaling only the last coordinate by `a₁` places our exact simplex inside
Ford's `S*`. All earlier coordinates, hence their band events, are preserved. -/
theorem shrinkLast_mem_fordSimplex {N : ℕ} {B : ℝ} {u : Fin (N+2) → ℝ}
    (hu : u ∈ prefixRegion (N+2) B 0 0) : shrinkLast N u ∈ fordSimplex N B := by
  have hnonneg := prefixRegion_nonneg hu
  have hle := shrinkLast_le hnonneg
  have ha : 0 < a 1 := a_pos le_rfl
  constructor
  · constructor
    · intro i
      by_cases hi : i = Fin.last (N+1)
      · subst i
        rw [prefixLinear_apply]
        have hs : (∑ j : Fin (N+2), if Fin.last (N+1) < j then
            a (j.val-(Fin.last (N+1)).val)*shrinkLast N u j else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          exact ite_eq_right (not_lt_of_ge (Fin.le_last j))
        rw [hs, sub_zero, shrinkLast_apply]
        simp only [ite_true]
        exact mul_nonneg ha.le (hnonneg _)
      · have hh := hu.1 i
        rw [prefixLinear_apply] at hh ⊢
        rw [shrinkLast_apply, ite_eq_right hi, one_mul]
        apply le_trans hh
        apply sub_le_sub_left
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hij
        · exact mul_le_mul_of_nonneg_left (hle j) (a_pos (by have := hij; simp only [Fin.lt_def] at this; omega)).le
        · exact le_rfl
    · have hh := hu.2
      simp only [sub_zero] at hh ⊢
      apply le_trans _ hh
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hle i) (a_pos (by omega)).le
  · have hh := hu.1 ⟨N, by omega⟩
    rw [prefixLinear_apply] at hh
    have hs : (∑ j : Fin (N+2), if (⟨N, by omega⟩ : Fin (N+2)) < j then
        a (j.val-N)*u j else 0) = a 1*u (Fin.last (N+1)) := by
      rw [Finset.sum_eq_single (Fin.last (N+1))]
      · have hlt : (⟨N, by omega⟩ : Fin (N+2)) < Fin.last (N+1) := by
          change N < N+1
          omega
        simp only [hlt, ite_true, Fin.val_last, Nat.add_sub_cancel_left]
      · intro j _ hj
        rw [ite_eq_right]
        simp only [Fin.lt_def]
        have hval : j.val ≠ N+1 := by
          intro he
          apply hj
          exact Fin.ext he
        have := j.isLt
        omega
      · simp
    rw [hs] at hh
    change shrinkLast N u (Fin.last (N+1)) ≤ shrinkLast N u ⟨N, by omega⟩
    rw [shrinkLast_apply, shrinkLast_apply]
    simp only [ite_true]
    rw [ite_eq_right (by intro h; have he := congrArg Fin.val h; simp at he), one_mul]
    change 0 ≤ u ⟨N, by omega⟩-a 1*u (Fin.last (N+1)) at hh
    linarith

lemma shrinkLast_preserves_prefix (N : ℕ) (u : Fin (N+2) → ℝ) (i : Fin (N+2))
    (hi : i ≠ Fin.last (N+1)) : shrinkLast N u i = u i := by
  simp [shrinkLast_apply, hi]

/-- A measurable event in Ford's simplex bounds its preimage in our simplex,
with only the fixed Jacobian factor `1/a₁`. -/
theorem shrinkLast_volume_bound {N : ℕ} {B : ℝ}
    (S T : Set (Fin (N+2) → ℝ)) (hT : MeasurableSet T)
    (hS : ∀ u ∈ S, u ∈ prefixRegion (N+2) B 0 0)
    (hST : ∀ u ∈ S, shrinkLast N u ∈ T) :
    volume S ≤ ENNReal.ofReal ((a 1)⁻¹)*volume (fordSimplex N B ∩ T) := by
  have ha := a_pos (j := 1) le_rfl
  have hford : MeasurableSet (fordSimplex N B) := by
    change MeasurableSet (prefixRegion (N+2) B 0 0 ∩
      {u : Fin (N+2) → ℝ | u (Fin.last (N+1)) ≤ u ⟨N, by omega⟩})
    exact (measurableSet_prefixRegion _ _ _ _).inter
      (measurableSet_le (measurable_pi_apply (Fin.last (N+1)))
        (measurable_pi_apply (⟨N, by omega⟩ : Fin (N+2))))
  have hincl : S ⊆ (shrinkLast N) ⁻¹' (fordSimplex N B ∩ T) := by
    intro u hu
    exact ⟨shrinkLast_mem_fordSimplex (hS u hu), hST u hu⟩
  apply (measure_mono hincl).trans_eq
  rw [← Measure.map_apply (shrinkLast N).continuous_of_finiteDimensional.measurable (hford.inter hT),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [shrinkLast_det]; exact ha.ne'),
    shrinkLast_det, Measure.smul_apply, smul_eq_mul, abs_of_pos (inv_pos.mpr ha)]

end TotientAsymptotic

end

end OAI
