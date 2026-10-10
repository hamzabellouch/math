import Mathlib
import OAI.Analysis.Commutator.CyclicCorner
import OAI.Analysis.Commutator.ReducingRepresentation

namespace OAI

noncomputable section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMap

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))] (ξ : H)

def cyclicRepresentation : S →⋆ₐ[ℂ] (cyclicSubspace S ξ →L[ℂ] cyclicSubspace S ξ) :=
  ReducingRepresentation.restrict (A := S) S.subtype (cyclicSubspace S ξ)
    (fun a : S => cyclicSubspace_invariant S ξ a.property)

@[simp] lemma cyclicRepresentation_apply (a : S) (x : cyclicSubspace S ξ) :
    (cyclicRepresentation S ξ a x:H)=(a:H →L[ℂ] H) x := rfl

def cyclicCornerVector (p : S) (hξ : (p:H →L[ℂ] H) ξ=ξ) :
    MatrixCornerHilbert.fixedSpace (cyclicRepresentation S ξ p) :=
  ⟨⟨ξ,mem_cyclicSubspace_self S ξ⟩,(MatrixCornerHilbert.mem_fixedSpace _ _).mpr (Subtype.ext hξ)⟩

theorem cyclicCornerVector_cyclic (p : S) (hp : IsStarProjection p)
    (hξ : (p:H →L[ℂ] H) ξ=ξ) :
    DenseRange (fun a : Corner hp => ReducingRepresentation.corner (cyclicRepresentation S ξ) hp a
      (cyclicCornerVector S ξ p hξ)) := by
  let K := cyclicSubspace S ξ
  let E := MatrixCornerHilbert.fixedSpace (cyclicRepresentation S ξ p)
  let m : E → H := fun x => ((x:K):H)
  let act : Corner hp → E := fun a => ReducingRepresentation.corner (cyclicRepresentation S ξ) hp a
    (cyclicCornerVector S ξ p hξ)
  have hm : Topology.IsEmbedding m :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have himage : m '' Set.range act = (cornerOrbit S (p:H →L[ℂ] H) ξ : Set H) := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨((a:S):H →L[ℂ] H),(a:S).property,
        congrArg (fun b : S => (b:H →L[ℂ] H)) a.property.1,
        congrArg (fun b : S => (b:H →L[ℂ] H)) a.property.2,rfl⟩
    · rintro ⟨a,ha,hpa,hap,rfl⟩
      let ac : Corner hp := ⟨⟨a,ha⟩,Subtype.ext hpa,Subtype.ext hap⟩
      exact ⟨act ac,⟨ac,rfl⟩,rfl⟩
  intro x
  change x∈closure (Set.range act)
  rw [hm.closure_eq_preimage_closure_image,himage]
  change m x∈(cornerOrbit S (p:H →L[ℂ] H) ξ).topologicalClosure
  apply (mem_cornerOrbit_closure_iff S
    (congrArg (fun b : S => (b:H →L[ℂ] H)) hp.isIdempotentElem.eq) p.property hξ (m x)).mpr
  exact ⟨(x:K).property,congrArg (fun y : K => (y:H))
    (MatrixCornerHilbert.fixed_apply (cyclicRepresentation S ξ p) x)⟩

end Kadison
end
end

end OAI
