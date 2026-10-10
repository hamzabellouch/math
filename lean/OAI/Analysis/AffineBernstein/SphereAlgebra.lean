import Mathlib
import OAI.Analysis.AffineBernstein.SphereIntegration

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Ambient expression for the round divergence of the restriction to the unit sphere. -/
def roundDivergence (b : OrthonormalBasis ι ℝ E) (W : E → E) (e : E) : ℝ :=
  ∑ i, inner ℝ (b i) (fderiv ℝ W e (b i - inner ℝ e (b i) • e))

theorem rotationGenerator_apply (u v e : E) :
    rotationGenerator u v e = inner ℝ u e • v - inner ℝ v e • u := rfl

theorem sum_rotation_pair_first (b : OrthonormalBasis ι ℝ E) (e w : E) :
    (∑ i, ∑ j, inner ℝ (b i) (rotationGenerator (b i) (b j) e) * inner ℝ (b j) w) =
      (1 - (Fintype.card ι : ℝ)) * inner ℝ e w := by
  have hb (i j : ι) : inner ℝ (b i) (b j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal i j
  simp only [rotationGenerator_apply, inner_sub_right, real_inner_smul_right, hb,
    sub_mul, Finset.sum_sub_distrib]
  have hew : (∑ i, inner ℝ (b i) e * inner ℝ (b i) w) = inner ℝ e w := by
    simpa only [real_inner_comm e] using b.sum_inner_mul_inner e w
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const, nsmul_eq_mul]
  rw [hew, Finset.card_univ]
  ring

omit [DecidableEq ι] in
theorem sum_rotation_pair_second (b : OrthonormalBasis ι ℝ E)
    (e : E) (he : inner ℝ e e = 1) (M : E →L[ℝ] E) :
    (∑ i, ∑ j, inner ℝ (b i) e * inner ℝ (b j) (M (rotationGenerator (b i) (b j) e))) =
      (∑ j, inner ℝ (b j) (M (b j))) - inner ℝ e (M e) := by
  simp only [rotationGenerator_apply, map_sub, map_smul, inner_sub_right,
    real_inner_smul_right, mul_sub, Finset.sum_sub_distrib]
  have hnorm : (∑ i, inner ℝ (b i) e * inner ℝ (b i) e) = 1 := by
    rw [← he]; simpa only [real_inner_comm e] using b.sum_inner_mul_inner e e
  have hdiag : (∑ i, ∑ j, inner ℝ (b i) e *
      (inner ℝ (b i) e * inner ℝ (b j) (M (b j)))) = ∑ j, inner ℝ (b j) (M (b j)) := by
    simp_rw [← mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul, hnorm, one_mul]
  have hcross : (∑ i, ∑ j, inner ℝ (b i) e *
      (inner ℝ (b j) e * inner ℝ (b j) (M (b i)))) = inner ℝ e (M e) := by
    simp_rw [← Finset.mul_sum]
    have hinner (i : ι) : (∑ j, inner ℝ (b j) e * inner ℝ (b j) (M (b i))) =
        inner ℝ e (M (b i)) := by
      simpa only [real_inner_comm e] using b.sum_inner_mul_inner e (M (b i))
    simp_rw [hinner, ← real_inner_smul_right, ← map_smul]
    rw [← inner_sum, ← map_sum, b.sum_repr']
  rw [hdiag, hcross]

omit [FiniteDimensional ℝ E] [DecidableEq ι] in
theorem roundDivergence_trace (b : OrthonormalBasis ι ℝ E) (W : E → E) (e : E) :
    roundDivergence b W e =
      (∑ i, inner ℝ (b i) (fderiv ℝ W e (b i))) - inner ℝ e (fderiv ℝ W e e) := by
  simp only [roundDivergence, map_sub, map_smul, inner_sub_right,
    real_inner_smul_right, Finset.sum_sub_distrib]
  rw [b.sum_inner_mul_inner]

/- Contraction of the rotation derivatives is divergence minus the normal correction. -/
theorem sum_rotation_pair (b : OrthonormalBasis ι ℝ E) (e : E)
    (he : inner ℝ e e = 1) (w : E) (M : E →L[ℝ] E) :
    (∑ i, ∑ j, (inner ℝ (b i) (rotationGenerator (b i) (b j) e) * inner ℝ (b j) w +
      inner ℝ (b i) e * inner ℝ (b j) (M (rotationGenerator (b i) (b j) e)))) =
      (∑ j, inner ℝ (b j) (M (b j))) - inner ℝ e (M e) +
        (1 - (Fintype.card ι : ℝ)) * inner ℝ e w := by
  simp only [Finset.sum_add_distrib]
  rw [sum_rotation_pair_first, sum_rotation_pair_second b e he M]
  ring

end AffineBernstein
end

end OAI
