import OAI.Geometry.RCD.Sobolev.CompactPointedTestRecovery
import OAI.Geometry.RCD.Sobolev.LocalGradientLipschitz

namespace OAI

/-! # Actual zero-boundary Sobolev recovery of Euclidean tests

The recovered function belongs to the original Dirichlet space. Both its
uniform value error and its rescaled gradient bound are explicit.
-/

open Set Metric Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_sobolev_test_recovery {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {p : X} {r S ρ a b ε B : ℝ}
    (hr : 0<r) (hρ : 0≤ρ) (hρa : ρ<a) (hab : a<b) (hbS : b<S)
    (hε : 0≤ε) (hsmall : 2*ε<a-ρ) (hB : 0≤B)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {ψ : Euclidean n → ℝ} {M : ℝ≥0} (hψ : LipschitzWith M ψ)
    (hψb : ∀ z, |ψ z|≤B) (hψ0 : ∀ z, ρ≤‖z‖ → ψ z=0) :
    ∃ (w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p (S*r))) (L : ℝ≥0),
      r*(L:ℝ)≤M+(B+M*ε)/(b-a) ∧
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val x|≤B+M*ε) ∧
      (∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic w.val x≤L) ∧
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p (S*r)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val x-ψ (v x)|≤M*ε := by
  let μ := hausdorff n X
  let := hX.separable
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨F,L,hF,hFc,hFs,hFb,hFL,hFe⟩ := compact_pointed_test_recovery hr hρ hρa hab hbS
    hε hsmall hB hv hψ hψb hψ0
  let w0 := SobolevSpace.ofLipschitzCompact μ hX.quadratic hF hFc
  have hrep : SobolevSpace.toLp μ hX.quadratic w0 =ᵐ[μ] F :=
    SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hF hFc
  have hdir : w0∈SobolevSpace.dirichlet μ hX.quadratic (ball p (S*r)) :=
    (SobolevSpace.dirichletCore μ hX.quadratic (ball p (S*r))).le_topologicalClosure
      ⟨F,L,hF,hFc,hFs,hrep⟩
  refine ⟨⟨w0,hdir⟩,L,hFL,?_,?_,?_⟩
  · filter_upwards [hrep] with x hx
    rw [hx]
    exact hFb x
  · exact SobolevSpace.minimalSlope_le_lipschitz μ hX.quadratic w0 hF hrep
  · filter_upwards [ae_restrict_of_ae hrep,ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx]
    exact hFe x (show dist x p≤S*r from (show dist x p<S*r from hball).le)

end RegularPointCoordinates

end

end OAI
