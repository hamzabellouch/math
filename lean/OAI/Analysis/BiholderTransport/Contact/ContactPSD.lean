import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Inner
import OAI.Analysis.BiholderTransport.Coordinates.Add
import OAI.Analysis.BiholderTransport.Coordinates.Stationary
import OAI.Analysis.BiholderTransport.LinearAlgebra.ContactDifferential

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactPSD
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma normalCost_quadraticExpansion {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    HasQuadraticExpansion (normalCost x p) (-p) (normalHessianOperator x p) := by
  rw [hasQuadraticExpansion_iff_isLittleO]
  have H := contDiffAt_second_order_remainder ((normalCost_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  convert H using 1
  funext h
  rw [(normalCost_hasFDerivAt_zero hp).fderiv]
  simp only [quadraticTaylor,innerSL_apply_apply,inner_normalHessianOperator,normalHessian]
  ring

omit [MeasurableSpace M] [BorelSpace M] in
lemma normal_contact_hessian_posSemidef
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈activeLogs (n := n) v x) (hpI : p∈injectivityDomain x)
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A)
    (e : TangentSpace 𝓘(ℝ,Model n) x) :
    0 ≤ inner ℝ ((normalHessianOperator x p+A) e) e := by
  have H := (normalCost_quadraticExpansion hpI).add hexp
  rw [neg_add_cancel] at H
  apply H.nonneg_of_localMin _ e
  apply Filter.Eventually.of_forall
  intro h
  have hgap := cTransform_gap_nonneg hv (riemannianExp x h) (riemannianExp x p)
  have heq := hp.2
  simp only [contactGap,normalCost,riemannianExp_zero] at heq ⊢ hgap
  linarith

end ContactPSD
end WeakMTWTransport

end

end

end

end OAI
