import Mathlib
import OAI.Computability.VertexCover.Reduction.HonestLargeSumIndependent
import OAI.Computability.VertexCover.Machines.Primitives
import OAI.Computability.VertexCover.Machines.ProfileSlot
import OAI.Computability.VertexCover.Machines.ProfileCompat
import OAI.Computability.VertexCover.Machines.NormRepresentation

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.LabelCover
abbrev TracePos (d : ℕ) := Bool × Fin d
abbrev ProfileRep (a b d : ℕ) := TracePos d × Query.Profile a b d
abbrev TraceWeights (a b d : ℕ) := TracePos d → Fin ((max a b)^(d-1)) → Fin (2*d+1)
abbrev Descriptor (a b d : ℕ) :=
  (ProfileRep a b d → Bool) × ((TracePos d × TracePos d → Bool) ×
    ((ProfileRep a b d × ProfileRep a b d → Bool) × TraceWeights a b d))
namespace Descriptor
variable {a b d : ℕ}
abbrev Rep (D : Descriptor a b d) := {r : ProfileRep a b d // D.1 r=true}
noncomputable def slot (D : Descriptor a b d) (r : ProfileRep a b d) : ℕ := by
  classical
  exact (Finset.univ.toList.filter (fun P => D.1 (r.1,P))).idxOf r.2
noncomputable def term (D : Descriptor a b d) (r : ProfileRep a b d) : ℝ :=
  ∑ x : TracePos d, if D.2.1 (x,r.1)=true then
    if h : D.slot r < (max a b)^(d-1) then (gridRational d (D.2.2.2 x ⟨D.slot r,h⟩) : ℝ) else 0
    else 0
def Good (D : Descriptor a b d) (S : Finset D.Rep) : Prop :=
  (∀ r ∈ S, ∀ s ∈ S, D.2.1 (r.val.1,s.val.1)=true → r=s) ∧
  (∀ r ∈ S, ∀ s ∈ S, D.2.2.1 (r.val,s.val)=true)
noncomputable def test (t : ℝ) (D : Descriptor a b d) : Bool := by
  classical
  exact decide (∀ S : Finset D.Rep, D.Good S → |∑ r ∈ S, D.term r.val| ≤ 2*t)
end Descriptor

variable {Φ : LabelCover} {d : ℕ}
def diagram (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d) : Descriptor Φ.qU Φ.qV d :=
  (fun r => decide ((Q r.1).ProfileValid r.2),
    (fun xy => decide (Q xy.1=Q xy.2), (fun rs => decide (Query.ProfilePair (Q rs.1.1) (Q rs.2.1) rs.1.2 rs.2.2),W)))
noncomputable def diagramCoordinate (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (r : (diagram Q W).Rep) : Φ.Coordinate d :=
  ⟨Q r.val.1,(Q r.val.1).decode r.val.2 (of_decide_eq_true r.property)⟩
noncomputable def diagramSum (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d) : Φ.Coordinate d → ℝ :=
  ∑ x, Φ.increment (Q x) (fun k => (gridRational d (W x ((Q x).slotPermutation k)) : ℝ))
 theorem diagram_coordinate_encode (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (r : (diagram Q W).Rep) : (Q r.val.1).encode (diagramCoordinate Q W r).2=r.val.2 :=
  (Q r.val.1).encode_decode r.val.2 (of_decide_eq_true r.property)
 theorem diagram_slot (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (r : (diagram Q W).Rep) : (diagram Q W).slot r.val=((Q r.val.1).profileSlot (diagramCoordinate Q W r).2).val := by
  classical
  simp only [Descriptor.slot,diagram,Query.profileSlot,Query.profileLabels,diagram_coordinate_encode]
 theorem diagram_term (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (r : (diagram Q W).Rep) : (diagram Q W).term r.val=diagramSum Q W (diagramCoordinate Q W r) := by
  classical
  rw [Descriptor.term]
  simp only [diagramSum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  change (if decide (Q x=Q r.val.1)=true then
    if h : (diagram Q W).slot r.val < Φ.WeightDimension d then
      (gridRational d (W x ⟨_,h⟩) : ℝ) else 0 else 0)=_
  simp only [decide_eq_true_eq]
  by_cases h : Q x=Q r.val.1
  · have hs := diagram_slot Q W r
    have ht : (diagram Q W).slot r.val < Φ.WeightDimension d := hs.symm ▸ ((Q r.val.1).profileSlot _).isLt
    rw [ite_eq_left h,dite_eq_left ht]
    simp only [h,diagramCoordinate,increment_same,Query.slotPermutation_apply]
    exact congrArg (fun k => (gridRational d (W x k) : ℝ)) (Fin.ext hs)
  · rw [ite_eq_right h]
    exact (Φ.increment_other (Q x) _ (diagramCoordinate Q W r) (Ne.symm h)).symm
 theorem diagram_good (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d)
    (S : Finset (diagram Q W).Rep) :
    (diagram Q W).Good S ↔ Set.InjOn (diagramCoordinate Q W) S ∧
      Φ.Compatible (S.image (diagramCoordinate Q W)) := by
  classical
  have pair (r s : (diagram Q W).Rep) :
      (diagram Q W).2.2.1 (r.val,s.val)=true ↔
        Query.LabelPair (diagramCoordinate Q W r).1 (diagramCoordinate Q W s).1
          (diagramCoordinate Q W r).2 (diagramCoordinate Q W s).2 := by
    simp only [diagram,decide_eq_true_eq]
    rw [← diagram_coordinate_encode Q W r,← diagram_coordinate_encode Q W s]
    exact Query.profilePair_iff _ _ _ _
  constructor
  · rintro ⟨hu,hp⟩
    have hi : Set.InjOn (diagramCoordinate Q W) S := by
      intro r hr s hs he
      exact hu r hr s hs (by simp only [diagram,decide_eq_true_eq]; exact congrArg Sigma.fst he)
    refine ⟨hi,(Φ.compatible_pair_iff _).mpr ⟨?_,?_⟩⟩
    · intro p hp' q hq' he
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp'
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hq'
      exact congrArg (diagramCoordinate Q W) (hu r hr s hs (by change Q r.val.1=Q s.val.1 at he; exact decide_eq_true he))
    · intro p hp' q hq'
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp'
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hq'
      exact (pair r s).mp (hp r hr s hs)
  · rintro ⟨hi,hc⟩
    obtain ⟨hu,hp⟩ := (Φ.compatible_pair_iff _).mp hc
    refine ⟨?_,?_⟩
    · intro r hr s hs he
      exact hi hr hs (hu _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩) _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
        (by change decide (Q r.val.1=Q s.val.1)=true at he; exact of_decide_eq_true he))
    · intro r hr s hs
      exact (pair r s).mpr (hp _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩) _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩))
 theorem diagram_test (Q : TracePos d → Φ.Query d) (W : TraceWeights Φ.qU Φ.qV d) (t : ℝ) :
    (diagram Q W).test t=true ↔ Φ.compatibilityNorm (diagramSum Q W) ≤ 2*t := by
  classical
  let B := Finset.univ.image Q
  have hz (p : Φ.Coordinate d) (hp : p.1 ∉ B) : diagramSum Q W p=0 := by
    simp only [diagramSum,Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro x _
    exact Φ.increment_other _ _ _ (fun he => hp (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,he.symm⟩))
  have hc (p : Φ.Coordinate d) (hp : p.1 ∈ B) : ∃ r, diagramCoordinate Q W r=p := by
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hp
    rcases p with ⟨i,A⟩
    dsimp at hx
    subst i
    let r : (diagram Q W).Rep := ⟨(x,(Q x).encode A),decide_eq_true ((Q x).encode_valid A)⟩
    refine ⟨r,?_⟩
    change (⟨Q x,(Q x).decode ((Q x).encode A) _⟩ : Φ.Coordinate d)=⟨Q x,A⟩
    congr 1
    apply (Q x).encode_injective
    exact (Q x).encode_decode _ _
  rw [Φ.norm_le_representations (diagramCoordinate Q W) _ B hz hc]
  simp only [Descriptor.test,decide_eq_true_eq,diagram_term]
  constructor
  · intro h S hi hs; exact h S ((diagram_good Q W S).mpr ⟨hi,hs⟩)
  · intro h S hs
    obtain ⟨hi,hc'⟩ := (diagram_good Q W S).mp hs
    exact h S hi hc'
end VertexCover.LabelCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
