import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringLabels
import OAI.Computability.VertexCover.Analysis.Restriction

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

namespace VertexCover.LabelCover.Query

variable {Φ : LabelCover} {d : ℕ}
abbrev Profile (a b d : ℕ) := (Fin d → Fin a) × (Fin d → Fin b)
def encodeAssignment (i : Φ.Query d) (A : i.Assignment) : Profile Φ.qU Φ.qV d :=
  (fun k => if h : i.1 < k then A.1 ⟨i.2.1 ⟨k,h⟩,Finset.mem_image.mpr ⟨⟨k,h⟩,by simp,rfl⟩⟩ else ⟨0,Φ.qU_pos⟩,
   fun k => if h : k < i.1 then A.2 ⟨i.2.2 ⟨k,h⟩,Finset.mem_image.mpr ⟨⟨k,h⟩,by simp,rfl⟩⟩ else ⟨0,Φ.qV_pos⟩)
def encode (i : Φ.Query d) (A : i.LocalLabel) : Profile Φ.qU Φ.qV d := encodeAssignment i A.val
@[simp] theorem encode_u (i : Φ.Query d) (A : i.Assignment) (k : Fin d) (h : i.1 < k) :
    (i.encodeAssignment A).1 k = A.1 ⟨i.2.1 ⟨k,h⟩,Finset.mem_image.mpr ⟨⟨k,h⟩,by simp,rfl⟩⟩ :=
  dite_eq_left h
@[simp] theorem encode_v (i : Φ.Query d) (A : i.Assignment) (k : Fin d) (h : k < i.1) :
    (i.encodeAssignment A).2 k = A.2 ⟨i.2.2 ⟨k,h⟩,Finset.mem_image.mpr ⟨⟨k,h⟩,by simp,rfl⟩⟩ :=
  dite_eq_left h
 theorem encodeAssignment_injective (i : Φ.Query d) : Function.Injective i.encodeAssignment := by
  intro A B h
  apply Prod.ext
  · funext x
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp x.property
    have hh := congrArg (fun P : Profile Φ.qU Φ.qV d => P.1 k) h
    simp only [encode_u i _ k k.property] at hh
    have he : (⟨i.2.1 k,Finset.mem_image.mpr ⟨k,by simp,rfl⟩⟩ : {x // x ∈ i.scopeU})=x := Subtype.ext hk
    simpa only [he] using hh
  · funext y
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp y.property
    have hh := congrArg (fun P : Profile Φ.qU Φ.qV d => P.2 k) h
    simp only [encode_v i _ k k.property] at hh
    have he : (⟨i.2.2 k,Finset.mem_image.mpr ⟨k,by simp,rfl⟩⟩ : {y // y ∈ i.scopeV})=y := Subtype.ext hk
    simpa only [he] using hh
 theorem encode_injective (i : Φ.Query d) : Function.Injective i.encode := by
  intro A B h
  exact Subtype.ext (i.encodeAssignment_injective h)

def ProfileValid (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) : Prop :=
  (∀ k, ¬i.1 < k → P.1 k=⟨0,Φ.qU_pos⟩) ∧
  (∀ k, ¬k < i.1 → P.2 k=⟨0,Φ.qV_pos⟩) ∧
  (∀ k l : {k : Fin d // i.1 < k}, i.2.1 k=i.2.1 l → P.1 k=P.1 l) ∧
  (∀ k l : {k : Fin d // k < i.1}, i.2.2 k=i.2.2 l → P.2 k=P.2 l) ∧
  (∀ c : Fin Φ.M, ∀ k : {k : Fin d // i.1 < k}, ∀ l : {k : Fin d // k < i.1},
    Φ.left c=i.2.1 k → Φ.right c=i.2.2 l → Φ.projection c (P.1 k)=P.2 l)
instance (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) : Decidable (i.ProfileValid P) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
 theorem encode_valid (i : Φ.Query d) (A : i.LocalLabel) : i.ProfileValid (i.encode A) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k hk; exact dite_eq_right hk
  · intro k hk; exact dite_eq_right hk
  · intro k l he
    simp only [encode,encode_u i _ k k.property,encode_u i _ l l.property]
    exact congrArg A.val.1 (Subtype.ext he)
  · intro k l he
    simp only [encode,encode_v i _ k k.property,encode_v i _ l l.property]
    exact congrArg A.val.2 (Subtype.ext he)
  · intro c k l hx hy
    simp only [encode,encode_u i _ k k.property,encode_v i _ l l.property]
    have hc := A.property c (hx.symm ▸ Finset.mem_image.mpr ⟨k,by simp,rfl⟩)
      (hy.symm ▸ Finset.mem_image.mpr ⟨l,by simp,rfl⟩)
    have ex : (⟨i.2.1 k,Finset.mem_image.mpr ⟨k,by simp,rfl⟩⟩ : {x // x ∈ i.scopeU}) =
        ⟨Φ.left c,hx.symm ▸ Finset.mem_image.mpr ⟨k,by simp,rfl⟩⟩ := Subtype.ext hx.symm
    have ey : (⟨i.2.2 l,Finset.mem_image.mpr ⟨l,by simp,rfl⟩⟩ : {y // y ∈ i.scopeV}) =
        ⟨Φ.right c,hy.symm ▸ Finset.mem_image.mpr ⟨l,by simp,rfl⟩⟩ := Subtype.ext hy.symm
    rw [ex,ey]
    exact hc

noncomputable def positionU (i : Φ.Query d) (x : {x // x ∈ i.scopeU}) : {k : Fin d // i.1 < k} :=
  (Finset.mem_image.mp x.property).choose
noncomputable def positionV (i : Φ.Query d) (y : {y // y ∈ i.scopeV}) : {k : Fin d // k < i.1} :=
  (Finset.mem_image.mp y.property).choose
 theorem positionU_eq (i : Φ.Query d) (x : {x // x ∈ i.scopeU}) : i.2.1 (i.positionU x)=x :=
  (Finset.mem_image.mp x.property).choose_spec.2
 theorem positionV_eq (i : Φ.Query d) (y : {y // y ∈ i.scopeV}) : i.2.2 (i.positionV y)=y :=
  (Finset.mem_image.mp y.property).choose_spec.2
noncomputable def decode (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) (hP : i.ProfileValid P) : i.LocalLabel :=
  ⟨(fun x => P.1 (i.positionU x),fun y => P.2 (i.positionV y)),fun c hx hy =>
    hP.2.2.2.2 c (i.positionU ⟨Φ.left c,hx⟩) (i.positionV ⟨Φ.right c,hy⟩)
      (i.positionU_eq ⟨Φ.left c,hx⟩).symm (i.positionV_eq ⟨Φ.right c,hy⟩).symm⟩
 theorem encode_decode (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) (hP : i.ProfileValid P) :
    i.encode (i.decode P hP)=P := by
  apply Prod.ext
  · funext k
    dsimp only [encode,encodeAssignment]
    split_ifs with hk
    · dsimp only [decode]
      exact hP.2.2.1 _ ⟨k,hk⟩ (i.positionU_eq ⟨i.2.1 ⟨k,hk⟩,Finset.mem_image.mpr ⟨⟨k,hk⟩,by simp,rfl⟩⟩)
    · exact (hP.1 k hk).symm
  · funext k
    dsimp only [encode,encodeAssignment]
    split_ifs with hk
    · dsimp only [decode]
      exact hP.2.2.2.1 _ ⟨k,hk⟩ (i.positionV_eq ⟨i.2.2 ⟨k,hk⟩,Finset.mem_image.mpr ⟨⟨k,hk⟩,by simp,rfl⟩⟩)
    · exact (hP.2.1 k hk).symm
 theorem valid_iff (i : Φ.Query d) (P : Profile Φ.qU Φ.qV d) :
    i.ProfileValid P ↔ ∃ A : i.LocalLabel, i.encode A=P := by
  constructor
  · intro h; exact ⟨i.decode P h,i.encode_decode P h⟩
  · rintro ⟨A,rfl⟩; exact i.encode_valid A
end VertexCover.LabelCover.Query
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
