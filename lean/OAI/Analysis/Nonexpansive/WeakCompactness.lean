import OAI.Analysis.Nonexpansive.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.Convex

namespace OAI

/-!
# Weak compactness from the actual canonical bidual map

The inverse of the surjective canonical inclusion is weak-star to weak
continuous because its scalar evaluations are precisely the evaluations
of the bidual. Banach–Alaoglu then gives weak compactness of norm balls.
Closed convex subsets are weakly closed by Hahn–Banach separation.
-/

noncomputable section

open Set Metric NormedSpace
open scoped Pointwise

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Continuous linear functionals separate points of the actual weak space. -/
theorem weakSpaceT2Space : T2Space (WeakSpace ℝ X) := by
  apply T2Space.of_injective_continuous
    (f := fun z : WeakSpace ℝ X =>
      fun f : StrongDual ℝ X => f ((toWeakSpace ℝ X).symm z))
  · intro z w h
    apply (toWeakSpace ℝ X).symm.injective
    exact (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr (fun f => congrFun h f)
  · exact WeakBilin.coeFn_continuous (topDualPairing ℝ X).flip

/-- The separate weak carrier inherits Hausdorffness from the weak space. -/
theorem weakCarrierT2Space (K : Set X) : T2Space (WeakCarrier K) := by
  let : T2Space (WeakSpace ℝ X) := weakSpaceT2Space
  infer_instance

/-- Norm-closed convex sets are closed in the actual weak topology. -/
theorem isClosed_toWeakSpace_image_of_closed_convex {K : Set X}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    IsClosed ((toWeakSpace ℝ X) '' K) := by
  apply closure_eq_iff_isClosed.mp
  rw [← hconvex.toWeakSpace_closure ℝ, hclosed.closure_eq]

theorem weaklyClosed_of_closed_convex {K : Set X}
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) : WeaklyClosed K :=
  isClosed_toWeakSpace_image_of_closed_convex hclosed hconvex

/-- Every norm closed ball is weakly closed, including an empty ball. -/
theorem weaklyClosed_closedBall (x : X) (r : ℝ) :
    WeaklyClosed (closedBall x r) :=
  weaklyClosed_of_closed_convex isClosed_closedBall (convex_closedBall x r)

private def bidualIsometryEquiv (hX : CanonicallyReflexive X) :
    X ≃ₗᵢ[ℝ] StrongDual ℝ (StrongDual ℝ X) :=
  LinearIsometryEquiv.ofSurjective (inclusionInDoubleDualLi ℝ) hX

private def weakBidualInverse (hX : CanonicallyReflexive X)
    (φ : WeakDual ℝ (StrongDual ℝ X)) : WeakSpace ℝ X :=
  toWeakSpace ℝ X ((bidualIsometryEquiv hX).symm (WeakDual.toStrongDual φ))

private theorem weakBidualInverse_eval (hX : CanonicallyReflexive X)
    (φ : WeakDual ℝ (StrongDual ℝ X)) (f : StrongDual ℝ X) :
    f ((toWeakSpace ℝ X).symm (weakBidualInverse hX φ)) = φ f := by
  have h := congrArg (fun ψ : StrongDual ℝ (StrongDual ℝ X) => ψ f)
    ((bidualIsometryEquiv hX).apply_symm_apply (WeakDual.toStrongDual φ))
  exact h

private theorem continuous_weakBidualInverse (hX : CanonicallyReflexive X) :
    Continuous (weakBidualInverse hX) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℝ X).flip
  intro f
  change Continuous (fun φ => f ((toWeakSpace ℝ X).symm (weakBidualInverse hX φ)))
  simpa only [weakBidualInverse_eval] using
    (WeakDual.eval_continuous (𝕜 := ℝ) (E := StrongDual ℝ X) f)

private theorem weakBidualInverse_image_closedBall
    (hX : CanonicallyReflexive X) (r : ℝ) :
    weakBidualInverse hX ''
        (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) r) =
      (toWeakSpace ℝ X) '' closedBall (0 : X) r := by
  ext x
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨(bidualIsometryEquiv hX).symm (WeakDual.toStrongDual φ), ?_, rfl⟩
    have hφ' : WeakDual.toStrongDual φ ∈
        closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) r := hφ
    simpa only [LinearIsometryEquiv.map_zero] using
      (bidualIsometryEquiv hX).symm.isometry.mapsTo_closedBall
        (0 : StrongDual ℝ (StrongDual ℝ X)) r hφ'
  · rintro ⟨x, hx, rfl⟩
    refine ⟨StrongDual.toWeakDual (bidualIsometryEquiv hX x), ?_, ?_⟩
    · change bidualIsometryEquiv hX x ∈ closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) r
      simpa only [LinearIsometryEquiv.map_zero] using
        (bidualIsometryEquiv hX).isometry.mapsTo_closedBall (0 : X) r hx
    · change toWeakSpace ℝ X
        ((bidualIsometryEquiv hX).symm (bidualIsometryEquiv hX x)) = toWeakSpace ℝ X x
      rw [LinearIsometryEquiv.symm_apply_apply]

/-- Canonical bidual surjectivity implies weak compactness of every ball.
No completeness or nontriviality assumption is needed for this implication. -/
theorem weaklyCompact_closedBall_zero (hX : CanonicallyReflexive X) (r : ℝ) :
    WeaklyCompact (closedBall (0 : X) r) := by
  have hc := WeakDual.isCompact_closedBall
    (𝕜 := ℝ) (E := StrongDual ℝ X) (0 : StrongDual ℝ (StrongDual ℝ X)) r
  have hi := hc.image (continuous_weakBidualInverse hX)
  rw [weakBidualInverse_image_closedBall hX r] at hi
  exact hi

/-- Every norm-closed bounded convex set in a canonically reflexive space
is weakly compact in the topology generated by its continuous dual. -/
theorem weaklyCompact_of_closed_bounded_convex (hX : CanonicallyReflexive X)
    {K : Set X} (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K)
    (hconvex : Convex ℝ K) : WeaklyCompact K := by
  obtain ⟨r, hr⟩ := hbounded.subset_closedBall (0 : X)
  exact (weaklyCompact_closedBall_zero hX r).of_isClosed_subset
    (weaklyClosed_of_closed_convex hclosed hconvex) (Set.image_mono hr)

theorem weaklyCompact_closedBall (hX : CanonicallyReflexive X) (x : X) (r : ℝ) :
    WeaklyCompact (closedBall x r) :=
  weaklyCompact_of_closed_bounded_convex hX isClosed_closedBall
    isBounded_closedBall (convex_closedBall x r)

/-- The weak carrier really is the subtype of the weak image. -/
theorem weakCarrier_set_eq_image (K : Set X) :
    {x : WeakSpace ℝ X | (toWeakSpace ℝ X).symm x ∈ K} =
      (toWeakSpace ℝ X) '' K := by
  ext x
  constructor
  · intro hx
    exact ⟨(toWeakSpace ℝ X).symm x, hx, (toWeakSpace ℝ X).apply_symm_apply x⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

/-- Transfer actual ambient weak compactness to the separate weak carrier. -/
theorem WeaklyCompact.compactSpace {K : Set X} (hK : WeaklyCompact K) :
    CompactSpace (WeakCarrier K) := by
  change CompactSpace {x : WeakSpace ℝ X | (toWeakSpace ℝ X).symm x ∈ K}
  apply isCompact_iff_compactSpace.mp
  rw [weakCarrier_set_eq_image]
  exact hK

theorem differenceBall_eq_inter (K : Set X) :
    differenceBall K = (differenceSpan K : Set X) ∩ closedBall (0 : X) 1 := by
  ext x
  simp only [differenceBall, mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_zero_right,
    SetLike.mem_coe]

theorem isClosed_differenceBall (K : Set X) : IsClosed (differenceBall K) := by
  rw [differenceBall_eq_inter]
  exact (Submodule.isClosed_topologicalClosure _).inter isClosed_closedBall

theorem isBounded_differenceBall (K : Set X) : Bornology.IsBounded (differenceBall K) := by
  rw [differenceBall_eq_inter]
  exact isBounded_closedBall.subset Set.inter_subset_right

theorem convex_differenceBall (K : Set X) : Convex ℝ (differenceBall K) := by
  rw [differenceBall_eq_inter]
  exact (differenceSpan K).convex.inter (convex_closedBall (0 : X) 1)

/-- Weak compactness of the entire unit ball of the closed difference span. -/
theorem weaklyCompact_differenceBall (hX : CanonicallyReflexive X) (K : Set X) :
    WeaklyCompact (differenceBall K) :=
  weaklyCompact_of_closed_bounded_convex hX (isClosed_differenceBall K)
    (isBounded_differenceBall K) (convex_differenceBall K)

end ReflexiveFixedPoints

end

end OAI
