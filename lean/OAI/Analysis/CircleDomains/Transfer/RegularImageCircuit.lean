import OAI.Analysis.CircleDomains.Topology.RegularJordanParametrization
import OAI.Analysis.CircleDomains.Sobolev.MixedCircuitSmoothness

namespace OAI

/-! The actual image of a regular source circuit is regular. No orientation
choice is needed here: the inverse differential prevents zero tangents. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsSmoothSphereEquivalence.regular_image_circuit
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi U V)
    (hU : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    {H J : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ U)
    (himage : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J)) :
    RegularJordanParametrization J (fun t => finiteCoord (f (γ t : Sphere))) := by
  let δ := fun t => finiteCoord (f (γ t : Sphere))
  let g := fun z : ℂ => finiteCoord (fi (z : Sphere))
  have hpoint (t : ℝ) : (γ t : Sphere) ∈ U :=
    hbd (mem_image_of_mem _ (hγ.mem_frontier t))
  have hfinite (t : ℝ) : f (γ t : Sphere) ≠ OnePoint.infty :=
    hf.finite_forward hU hfix (hpoint t)
  have hδ : ContDiff ℝ (⊤ : ℕ∞) δ := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((hf.smooth _ (hpoint t)).contDiffAt_finiteMap (hfinite t)).comp t
      hγ.smooth.contDiffAt
  have hleft : g ∘ δ = γ := by
    funext t
    simp only [Function.comp_apply, g, δ, coe_finiteCoord (hfinite t),
      hf.left_inv _ (hpoint t), finiteCoord_coe]
  refine ⟨hδ, fun t => congrArg (fun z : ℂ => finiteCoord (f (z : Sphere))) (hγ.periodic t),
    ?_, ?_, ?_⟩
  · intro x hx y hy he
    apply hγ.injective hx hy
    apply OnePoint.coe_injective
    apply hf.bijOn.injOn (hpoint x) (hpoint y)
    have hh := congrArg (fun z : ℂ => (z : Sphere)) he
    simpa only [δ, coe_finiteCoord (hfinite x), coe_finiteCoord (hfinite y)] using hh
  · intro t hz
    have hV : (δ t : Sphere) ∈ V := by
      simpa only [δ, coe_finiteCoord (hfinite t)] using hf.mapsTo (hpoint t)
    have hg : DifferentiableAt ℝ g (δ t) :=
      ((hf.smooth_inv _ hV).contDiffAt_finiteMap (hf.finite_inv hU hfix hV)).differentiableAt
        (by simp)
    have he := (hg.hasFDerivAt.comp_hasDerivAt t (hδ.differentiable (by simp) t).hasDerivAt).deriv
    rw [hleft, hz, map_zero] at he
    exact hγ.regular t he
  · apply Set.image_injective.mpr OnePoint.coe_injective
    calc
      ((↑) : ℂ → Sphere) '' (δ '' Icc 0 1) =
          f '' (((↑) : ℂ → Sphere) '' (γ '' Icc 0 1)) := by
        simp only [image_image]
        apply image_congr
        intro t _
        exact coe_finiteCoord (hfinite t)
      _ = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) := by
        rw [hγ.boundary, himage]

end CircleDomainRigidity

end

end OAI
