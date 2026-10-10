import OAI.Geometry.SurfaceImmersion.Geometry.LowJetSegment

namespace OAI

/-! A fixed compact enlargement contains the jets of every small correction segment. -/
noncomputable section
open Set
open scoped ContDiff Pointwise
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_segment_mem_add_closedBall {U : Set Base} (hU : IsOpen U)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {K : Set LowJet} (hmap : MapsTo (lowJet G) U K)
    {τ δ C : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ) (hδτ : δ ≤ τ) (hC : 0 ≤ C)
    (hHb : WeightedBound U τ 2 (C*δ*τ) H) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    MapsTo (lowJet (fun x => G x+t • H x)) U (K+Metric.closedBall 0 C) := by
  have hc : (C*δ*τ)/τ^2 ≤ C := by
    apply (div_le_iff₀ (sq_pos_of_pos hτ)).2
    nlinarith only [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hδτ hτ.le) hC]
  have hv := weighted_variationLowJet hU hH hτ hτ1
    (mul_nonneg (mul_nonneg hC hδ) hτ.le) 0 hHb
  intro x hx
  rw [lowJet_affine hG hH t x]
  apply Set.add_mem_add (hmap hx)
  rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans ((hv.norm_le hx).trans hc)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
