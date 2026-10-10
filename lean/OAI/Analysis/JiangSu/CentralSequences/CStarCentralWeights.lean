import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace CStarCentralWeights
open scoped InnerProductSpace WithCStarModule

variable {E : Type*} [NonUnitalCStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
variable {ι : Type*} [Fintype ι]

lemma weighted_row_bound (v y : ι → E) {C : ℝ} (hC : 0 ≤ C)
    (hy : ∀ i, ‖y i‖ ≤ C) :
    ‖∑ i, v i * y i * star (y i) * star (v i)‖ ≤
      C^2 * ‖∑ i, v i * star (v i)‖ := by
  have hpos : 0 ≤ ∑ i, v i * y i * star (y i) * star (v i) := by
    apply Finset.sum_nonneg
    intro i _
    simpa only [star_mul, mul_assoc] using mul_star_self_nonneg (v i * y i)
  have hle : (∑ i, v i * y i * star (y i) * star (v i)) ≤
      C^2 • (∑ i, v i * star (v i)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = v i * (y i * star (y i)) * star (v i) := by simp only [mul_assoc]
      _ ≤ ‖y i * star (y i)‖ • (v i * star (v i)) :=
        CStarAlgebra.star_right_conjugate_le_norm_smul (v i) (y i * star (y i))
      _ ≤ C^2 • (v i * star (v i)) := by
        apply smul_le_smul_of_nonneg_right _ (mul_star_self_nonneg _)
        rw [CStarRing.norm_self_mul_star]
        nlinarith [hy i, norm_nonneg (y i)]
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hpos
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg C)] using hn

lemma weighted_sum_bound (v y : ι → E) {C : ℝ} (hC : 0 ≤ C)
    (hv : ‖∑ i, v i * star (v i)‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ C) :
    ‖∑ i, v i * y i * star (v i)‖ ≤ C := by
  let x : WithCStarModule E (ι → E) := (WithCStarModule.equiv E _).symm v
  let z : WithCStarModule E (ι → E) := (WithCStarModule.equiv E _).symm (fun i => v i*y i)
  have hx : ‖x‖ ≤ 1 := by
    have he := WithCStarModule.pi_norm_sq x
    simp only [WithCStarModule.inner_def] at he
    change ‖x‖^2=‖∑ i,v i*star (v i)‖ at he
    nlinarith [norm_nonneg x]
  have hz : ‖z‖ ≤ C := by
    have he := WithCStarModule.pi_norm_sq z
    simp only [WithCStarModule.inner_def] at he
    change ‖z‖^2=‖∑ i,(v i*y i)*star (v i*y i)‖ at he
    simp only [star_mul, ←mul_assoc] at he
    have hn := weighted_row_bound v y hC hy
    have hm : C^2*‖∑ i,v i*star (v i)‖ ≤ C^2 := by nlinarith [sq_nonneg C]
    nlinarith [norm_nonneg z]
  have hn := CStarModule.norm_inner_le (A := E) (WithCStarModule E (ι → E)) (x := x) (y := z)
  simp only [WithCStarModule.pi_inner, WithCStarModule.inner_def] at hn
  change ‖∑ i,v i*y i*star (v i)‖ ≤ ‖x‖*‖z‖ at hn
  exact hn.trans (by nlinarith [norm_nonneg x,norm_nonneg z])

lemma central_weighted_sum_bound (v y : ι → E) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, IsSelfAdjoint (v i)) (hc : ∀ i, Commute (v i) (y i))
    (hp : ‖∑ i, v i * v i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ C) :
    ‖∑ i, (v i*v i) * y i‖ ≤ C := by
  have he : (∑ i, v i*y i*star (v i)) = ∑ i,(v i*v i)*y i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hv i).star_eq, mul_assoc, (hc i).symm.eq, ←mul_assoc]
  rw [←he]
  apply weighted_sum_bound v y hC _ hy
  simpa only [(hv _).star_eq] using hp

end CStarCentralWeights

end
end

end OAI
