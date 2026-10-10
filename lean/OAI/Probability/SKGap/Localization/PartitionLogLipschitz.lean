import Mathlib
import OAI.Probability.SKGap.Gaussian.PartitionSecondMoment

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

lemma finite_linear_lipschitz {κ : Type*} [Fintype κ] (a : κ→ℝ) {L : ℝ≥0}
    (ha : (∑ i,a i^2) ≤ (L:ℝ)^2) :
    LipschitzWith L (fun x : EuclideanSpace ℝ κ=>∑ i,a i*x i) := by
  have hn : ‖(WithLp.toLp 2 a : EuclideanSpace ℝ κ)‖ ≤ (L:ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).mp
    simpa only [EuclideanSpace.real_norm_sq_eq,PiLp.toLp_apply] using ha
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := norm_inner_le_norm (𝕜:=ℝ) (WithLp.toLp 2 a : EuclideanSpace ℝ κ) (x-y)
  have he : inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ κ) (x-y)=
      (∑ i,a i*x i)-(∑ i,a i*y i) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
    change (∑ i,(x i-y i)*a i)=(∑ i,a i*x i)-(∑ i,a i*y i)
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Real.dist_eq,← he]
  exact hh.trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (by rw [dist_eq_norm]))

lemma edge_card_real_le_square (n : ℕ) : (Fintype.card (Edge n):ℝ) ≤ (n:ℝ)^2 := by
  have h := Fintype.card_subtype_le (fun p : Fin n×Fin n=>p.1 < p.2)
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  exact_mod_cast (show Fintype.card (Edge n) ≤ n^2 by simpa only [sq] using h)

lemma gaussianSpinPartition_log_lipschitz {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hnr : (n:ℝ)*r ≤ 1) :
    LipschitzWith ⟨sqrt (n:ℝ),sqrt_nonneg _⟩ (fun x : EuclideanSpace ℝ (Edge n)=>
      log (gaussianSpinPartition n r x.ofLp)) := by
  change LipschitzWith ⟨sqrt (n:ℝ),sqrt_nonneg _⟩ (fun g : EuclideanSpace ℝ (Edge n)=>
    log (∑ x : Spin n,exp (∑ e,edgeCoefficient r x e*g e)))
  refine log_sum_exp_lipschitz (fun (x : Spin n) (g : EuclideanSpace ℝ (Edge n))=>∑ e,edgeCoefficient r x e*g e) ?_
  intro x
  apply finite_linear_lipschitz
  change (∑ e,edgeCoefficient r x e^2) ≤ (sqrt (n:ℝ))^2
  rw [edgeCoefficient_sq_sum hr,sq_sqrt (by positivity)]
  have hh := mul_le_mul_of_nonneg_left (edge_card_real_le_square n) hr
  nlinarith [mul_le_mul_of_nonneg_right hnr (show (0:ℝ) ≤ n by positivity)]
end SKGap
end
end

end OAI
