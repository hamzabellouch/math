import OAI.Analysis.KadisonKastler.StrictPinchingRefinement
import OAI.Analysis.KadisonKastler.DecreasingProjectionLimit

namespace OAI

/-! # Closed spaces attached to a family of projection cuts

The remaining left corner and the simultaneous commutation space are
intersections of concrete operator kernels. Their projections therefore
exist also for infinite families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def operatorKernelClosed (T : H →L[ℂ] H) : ClosedSubmodule ℂ H := ⟨T.ker,T.isClosed_ker⟩

def projectionFamilyRemainderSpace (S : Set (AlgebraProjection M)) : ClosedSubmodule ℂ H :=
  ⨅ p : S, operatorKernelClosed p.val.val.val

def projectionFamilyCommutationSpace (J : H ≃ₗᵢ⋆[ℂ] H)
    (S : Set (AlgebraProjection M)) : ClosedSubmodule ℂ H :=
  ⨅ p : S, operatorKernelClosed (p.val.val.val-conjugationOperator J p.val.val.val)

@[simp] theorem mem_projectionFamilyRemainderSpace (S : Set (AlgebraProjection M)) (x : H) :
    x ∈ projectionFamilyRemainderSpace S ↔ ∀ p ∈ S, p.val.val x=0 := by
  simp only [projectionFamilyRemainderSpace,ClosedSubmodule.mem_iInf,operatorKernelClosed,
    ClosedSubmodule.mem_mk,LinearMap.mem_ker,ContinuousLinearMap.coe_coe,Subtype.forall]

@[simp] theorem mem_projectionFamilyCommutationSpace (J : H ≃ₗᵢ⋆[ℂ] H)
    (S : Set (AlgebraProjection M)) (x : H) :
    x ∈ projectionFamilyCommutationSpace J S ↔
      ∀ p ∈ S, p.val.val x=conjugationOperator J p.val.val x := by
  simp only [projectionFamilyCommutationSpace,ClosedSubmodule.mem_iInf,operatorKernelClosed,
    ClosedSubmodule.mem_mk,LinearMap.mem_ker,ContinuousLinearMap.coe_coe,Subtype.forall,
    sub_apply,sub_eq_zero]

theorem projectionFamilyRemainderSpace_antitone :
    Antitone (projectionFamilyRemainderSpace (M := M)) := by
  intro S T hST x hx
  rw [mem_projectionFamilyRemainderSpace] at hx ⊢
  exact fun p hp => hx p (hST hp)

theorem projectionFamilyCommutationSpace_antitone (J : H ≃ₗᵢ⋆[ℂ] H) :
    Antitone (projectionFamilyCommutationSpace (M := M) J) := by
  intro S T hST x hx
  rw [mem_projectionFamilyCommutationSpace] at hx ⊢
  exact fun p hp => hx p (hST hp)

theorem projectionFamilyRemainderSpace_invariant (S : Set (AlgebraProjection M))
    (a : Algebra M.commutant) {x : H} (hx : x ∈ projectionFamilyRemainderSpace S) :
    a.val x ∈ projectionFamilyRemainderSpace S := by
  rw [mem_projectionFamilyRemainderSpace] at hx ⊢
  intro p hp
  have hc := congrArg (fun T : H →L[ℂ] H => T x)
    (VonNeumannAlgebra.mem_commutant_iff.mp a.property p.val.val p.val.property)
  change p.val.val (a.val x)=a.val (p.val.val x) at hc
  rw [hc,hx p hp,map_zero]

theorem projectionFamilyRemainderProjection_mem (S : Set (AlgebraProjection M)) :
    (projectionFamilyRemainderSpace S).toSubmodule.starProjection ∈ M := by
  have h : (projectionFamilyRemainderSpace S).toSubmodule.starProjection ∈ M.commutant.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact (starProjection_commutes_of_invariant (projectionFamilyRemainderSpace S).toSubmodule
      a (fun _ hx => projectionFamilyRemainderSpace_invariant S ⟨a,ha⟩ hx)
        (fun _ hx => projectionFamilyRemainderSpace_invariant S (star ⟨a,ha⟩) hx)).symm
  simpa only [M.commutant_commutant] using h

def projectionFamilyRemainder (S : Set (AlgebraProjection M)) : AlgebraProjection M :=
  ⟨⟨(projectionFamilyRemainderSpace S).toSubmodule.starProjection,
      projectionFamilyRemainderProjection_mem S⟩,
    ⟨Subtype.ext (Submodule.isIdempotentElem_starProjection _).eq,
      Subtype.ext (isSelfAdjoint_starProjection _).star_eq⟩⟩

def projectionFamilyPinching (J : H ≃ₗᵢ⋆[ℂ] H) (S : Set (AlgebraProjection M)) : H →L[ℂ] H :=
  (projectionFamilyCommutationSpace J S).toSubmodule.starProjection

theorem projectionFamilyPinching_isProjection (J : H ≃ₗᵢ⋆[ℂ] H)
    (S : Set (AlgebraProjection M)) : IsStarProjection (projectionFamilyPinching J S) :=
  ⟨Submodule.isIdempotentElem_starProjection _,isSelfAdjoint_starProjection _⟩

end

end KadisonKastler

end OAI
