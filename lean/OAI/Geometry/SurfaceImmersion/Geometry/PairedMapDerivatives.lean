import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveVelocities

namespace OAI

/-! Derivatives of a pair of maps with equal images under a surface map. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
variable {f : M → ProjectionTarget 3} {A B : N → M}

theorem regular_paired_map_derivatives
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hleft : ContMDiff 𝓘(ℝ) planeModel ∞ A)
    (hright : ContMDiff 𝓘(ℝ) planeModel ∞ B)
    (heq : ∀ q, f (A q) = f (B q)) (p : N)
    (hpair : Function.Injective ((mfderiv 𝓘(ℝ) planeModel A p).prod
      (mfderiv 𝓘(ℝ) planeModel B p)))
    (hA : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A p)))
    (hB : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B p))) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel A p) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel B p) ∧
      Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,ProjectionTarget 3) (f ∘ A) p) := by
  have heq' : (fun q : N => f (A q)) =
      (fun q : N => f (B q)) := by
    funext q
    exact heq q
  have hDA := mfderiv_comp p (hf.mdifferentiable (by simp)).mdifferentiableAt
    (hleft.mdifferentiable (by simp)).mdifferentiableAt
  have hDB := mfderiv_comp p (hf.mdifferentiable (by simp)).mdifferentiableAt
    (hright.mdifferentiable (by simp)).mdifferentiableAt
  have hrel :
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A p)).comp
        (mfderiv 𝓘(ℝ) planeModel A p) =
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B p)).comp
        (mfderiv 𝓘(ℝ) planeModel B p) := by
    have hev : (fun q : N => f (A q)) =ᶠ[𝓝 p]
        (fun q : N => f (B q)) := Filter.Eventually.of_forall (congrFun heq')
    have hd := hev.mfderiv_eq (I := 𝓘(ℝ)) (I' := 𝓘(ℝ,ProjectionTarget 3))
    apply ContinuousLinearMap.ext
    intro v
    have hdv := congrArg (fun L => L v) hd
    change (mfderiv 𝓘(ℝ) 𝓘(ℝ,ProjectionTarget 3)
        (f ∘ fun q : N => A q) p) v =
      (mfderiv 𝓘(ℝ) 𝓘(ℝ,ProjectionTarget 3)
        (f ∘ fun q : N => B q) p) v at hdv
    rw [hDA,hDB] at hdv
    exact hdv
  have hLA : Function.Injective (mfderiv 𝓘(ℝ) planeModel A p) := by
    intro u v huv
    apply hpair
    apply Prod.ext huv
    change (mfderiv 𝓘(ℝ) planeModel B p) u = (mfderiv 𝓘(ℝ) planeModel B p) v
    apply hB
    have hh := congrArg (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A p)) huv
    change ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A p)).comp
      (mfderiv 𝓘(ℝ) planeModel A p)) u =
      ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (A p)).comp
        (mfderiv 𝓘(ℝ) planeModel A p)) v at hh
    rw [hrel] at hh
    exact hh
  have hLB : Function.Injective (mfderiv 𝓘(ℝ) planeModel B p) := by
    intro u v huv
    apply hpair
    apply Prod.ext _ huv
    change (mfderiv 𝓘(ℝ) planeModel A p) u = (mfderiv 𝓘(ℝ) planeModel A p) v
    apply hA
    have hh := congrArg (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B p)) huv
    change ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B p)).comp
      (mfderiv 𝓘(ℝ) planeModel B p)) u =
      ((mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (B p)).comp
        (mfderiv 𝓘(ℝ) planeModel B p)) v at hh
    rw [← hrel] at hh
    exact hh
  refine ⟨hLA,hLB,?_⟩
  rw [hDA]
  exact hA.comp hLA

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
