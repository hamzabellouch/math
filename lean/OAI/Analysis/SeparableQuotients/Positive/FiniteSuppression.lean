import Mathlib

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Sampling
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]


lemma exists_halfNormer (f : StrongDual ℝ X) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ ‖f‖ ≤ 2 * |f x| := by
  by_cases hf : f = 0
  · exact ⟨0, by norm_num, by simp [hf]⟩
  have hp : 0 < ‖f‖ := norm_pos_iff.mpr hf
  obtain ⟨x, hx, hfx⟩ := f.exists_lt_apply_of_lt_opNorm (show ‖f‖ / 2 < ‖f‖ by linarith)
  refine ⟨x, hx.le, ?_⟩
  rw [Real.norm_eq_abs] at hfx
  linarith

def halfNormer (f : StrongDual ℝ X) : X :=
  if f = 0 then 0 else (exists_halfNormer f).choose

@[simp] lemma halfNormer_zero : halfNormer (0 : StrongDual ℝ X) = 0 := by
  simp [halfNormer]

lemma norm_halfNormer (f : StrongDual ℝ X) : ‖halfNormer f‖ ≤ 1 := by
  by_cases h : f = 0
  · simp [h]
  · simpa only [halfNormer, ite_eq_right h] using (exists_halfNormer f).choose_spec.1

lemma halfNormer_bound (f : StrongDual ℝ X) : ‖f‖ ≤ 2 * |f (halfNormer f)| := by
  by_cases h : f = 0
  · simp [h]
  · simpa only [halfNormer, ite_eq_right h] using (exists_halfNormer f).choose_spec.2

abbrev UnitBall (X : Type*) [NormedAddCommGroup X] := {x : X // ‖x‖ ≤ 1}
def ballHalfNormer (f : StrongDual ℝ X) : UnitBall X := ⟨halfNormer f, norm_halfNormer f⟩


lemma suppression_of_cross_vanishing {J : Type*} [Fintype J] (f : J → StrongDual ℝ X)
    (a : J → ℝ) (s : Finset J)
    (hzero : ∀ i, i ∉ s → f i (halfNormer (∑ j ∈ s, a j • f j)) = 0) :
    ‖∑ j ∈ s, a j • f j‖ ≤ 2 * ‖∑ j, a j • f j‖ := by
  let x := halfNormer (∑ j ∈ s, a j • f j)
  have he : (∑ j, a j • f j) x = (∑ j ∈ s, a j • f j) x := by
    simp only [sum_apply, smul_apply, smul_eq_mul]
    apply (Finset.sum_subset (Finset.subset_univ s) _).symm
    intro i _ hi
    rw [hzero i hi, mul_zero]
  have hb : |(∑ j, a j • f j) x| ≤ ‖∑ j, a j • f j‖ := by
    simpa only [Real.norm_eq_abs, mul_one] using
      (∑ j, a j • f j).le_opNorm_of_le (norm_halfNormer _)
  calc
    ‖∑ j ∈ s, a j • f j‖ ≤ 2 * |(∑ j ∈ s, a j • f j) x| := halfNormer_bound _
    _ = 2 * |(∑ j, a j • f j) x| := by rw [he]
    _ ≤ 2 * ‖∑ j, a j • f j‖ := mul_le_mul_of_nonneg_left hb (by norm_num)

end SeparableQuotient.Positive.Sampling

end

end

end OAI
