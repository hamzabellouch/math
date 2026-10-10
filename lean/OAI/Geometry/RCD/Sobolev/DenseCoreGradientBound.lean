import OAI.Geometry.RCD.Coordinates.RegularDirichletCore
import OAI.Geometry.RCD.Metric.IntegralSquareProduct
import OAI.Geometry.RCD.Sobolev.HessianActionLocality

namespace OAI

/-! # Recovering a gradient bound from tests in the dense regular core

Integral Cauchy--Schwarz and continuity of the restricted energy form avoid
any extra regularity requirement on the gradient-pairing representative.
-/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.gradient_integral_le_of_core_tests {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {Ω S : Set X} (hΩ : IsOpen Ω) (hS : MeasurableSet S)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (D : X → ℝ)
    (hD : Integrable D ((hausdorff n X).restrict S))
    (hD0 : ∀ᵐ x ∂(hausdorff n X).restrict S, 0≤D x)
    (hbound : ∀ g : compactLaplacianCore (hausdorff n X) hX.quadratic Ω,
      ∀ᵐ x ∂(hausdorff n X).restrict S,
        (localGamma (hausdorff n X) hX.quadratic f g.val x)^2≤
          D x*localGamma (hausdorff n X) hX.quadratic g.val g.val x)
    (v : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v.val
      =ᵐ[(hausdorff n X).restrict S] SobolevSpace.toLp (hausdorff n X) hX.quadratic f) :
    (∫ x in S, localGamma (hausdorff n X) hX.quadratic f f x ∂hausdorff n X)≤
      ∫ x in S, D x ∂hausdorff n X := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let w : X → ℝ := S.indicator (fun _ => 1)
  have hw : AEStronglyMeasurable w μ := (measurable_const.indicator hS).aestronglyMeasurable
  have hw1 : ∀ᵐ x ∂μ, ‖w x‖≤(1:ℝ≥0) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x∈S <;> simp [w,hx]
  let W := weightedGammaCLM μ hQ hw hw1
  have hW (a b : SobolevSpace μ hQ) : W a b=∫ x in S, localGamma μ hQ a b x ∂μ := by
    change (∫ x, w x*localGamma μ hQ a b x ∂μ)=_
    rw [← integral_indicator hS]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x∈S <;> simp [w,hx]
  let B := ∫ x in S, D x ∂μ
  have hclosed : IsClosed {g : SobolevSpace.dirichlet μ hQ Ω |
      (W f g.val)^2≤B*W g.val g.val} := by
    have hj : Continuous (fun g : SobolevSpace.dirichlet μ hQ Ω => g.val) :=
      (SobolevSpace.dirichlet μ hQ Ω).subtypeL.continuous
    exact isClosed_le (((W f).continuous.comp hj).pow 2)
      (continuous_const.mul ((W.continuous.comp hj).clm_apply hj))
  have hinc : (regularDirichletCore μ hQ Ω : Set (SobolevSpace.dirichlet μ hQ Ω)) ⊆
      {g | (W f g.val)^2≤B*W g.val g.val} := by
    intro g hg
    change g.val∈compactLaplacianCore μ hQ Ω at hg
    change (W f g.val)^2≤B*W g.val g.val
    rw [hW,hW]
    exact integral_sq_le_of_sq_le_product (μ.restrict S) hD
      (localGamma_memL1 μ hQ g.val g.val).integrableOn
      (localGamma_memL1 μ hQ f g.val).integrableOn hD0
      (by
        filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ g.val)] with x hx
        rw [hx]
        positivity)
      (hbound ⟨g.val,hg⟩)
  have hall := closure_minimal hinc hclosed
  rw [(hX.regularDirichletCore_dense hn hΩ).closure_eq] at hall
  have hineq := hall (mem_univ v)
  change (W f v.val)^2≤B*W v.val v.val at hineq
  have hfv := localGamma_pair_congr_ae μ hQ (f := f) (f' := f) EventuallyEq.rfl hv
  have hvv := localGamma_pair_congr_ae μ hQ hv hv
  rw [hW,hW,integral_congr_ae hfv,integral_congr_ae hvv] at hineq
  have hnonneg : 0≤∫ x in S, localGamma μ hQ f f x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ f)] with x hx
    rw [hx]
    positivity
  have hB : 0≤B := integral_nonneg_of_ae hD0
  rcases eq_or_lt_of_le hnonneg with hz | hp
  · rw [← hz]
    exact hB
  · exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [pow_two] using hineq)

end RegularPointCoordinates

end

end OAI
