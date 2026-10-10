import Mathlib
import OAI.Computability.VertexCover.Machines.Profile

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
def ProfilePair (i j : Φ.Query d) (P R : Profile Φ.qU Φ.qV d) : Prop :=
  (∀ k : {k : Fin d // i.1 < k}, ∀ l : {k : Fin d // j.1 < k},
    i.2.1 k=j.2.1 l → P.1 k=R.1 l) ∧
  (∀ k : {k : Fin d // k < i.1}, ∀ l : {k : Fin d // k < j.1},
    i.2.2 k=j.2.2 l → P.2 k=R.2 l) ∧
  (∀ c : Fin Φ.M, ∀ k : {k : Fin d // i.1 < k}, ∀ l : {k : Fin d // k < j.1},
    Φ.left c=i.2.1 k → Φ.right c=j.2.2 l → Φ.projection c (P.1 k)=R.2 l)
instance (i j : Φ.Query d) (P R : Profile Φ.qU Φ.qV d) : Decidable (ProfilePair i j P R) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def LabelPair (i j : Φ.Query d) (A : i.LocalLabel) (B : j.LocalLabel) : Prop :=
  (∀ x (hi : x ∈ i.scopeU) (hj : x ∈ j.scopeU), A.val.1 ⟨x,hi⟩=B.val.1 ⟨x,hj⟩) ∧
  (∀ y (hi : y ∈ i.scopeV) (hj : y ∈ j.scopeV), A.val.2 ⟨y,hi⟩=B.val.2 ⟨y,hj⟩) ∧
  (∀ c (hi : Φ.left c ∈ i.scopeU) (hj : Φ.right c ∈ j.scopeV),
    Φ.projection c (A.val.1 ⟨Φ.left c,hi⟩)=B.val.2 ⟨Φ.right c,hj⟩)
 theorem encode_at_u (i : Φ.Query d) (A : i.LocalLabel) (k : {k : Fin d // i.1 < k})
    (x : {x // x ∈ i.scopeU}) (h : i.2.1 k=x) : (i.encode A).1 k=A.val.1 x := by
  simp only [encode,encode_u i _ k k.property]
  exact congrArg A.val.1 (Subtype.ext h)
 theorem encode_at_v (i : Φ.Query d) (A : i.LocalLabel) (k : {k : Fin d // k < i.1})
    (y : {y // y ∈ i.scopeV}) (h : i.2.2 k=y) : (i.encode A).2 k=A.val.2 y := by
  simp only [encode,encode_v i _ k k.property]
  exact congrArg A.val.2 (Subtype.ext h)
 theorem profilePair_iff (i j : Φ.Query d) (A : i.LocalLabel) (B : j.LocalLabel) :
    ProfilePair i j (i.encode A) (j.encode B) ↔ LabelPair i j A B := by
  constructor
  · rintro ⟨hu,hv,hc⟩
    refine ⟨?_,?_,?_⟩
    · intro x hi hj
      have ei := i.positionU_eq ⟨x,hi⟩
      have ej := j.positionU_eq ⟨x,hj⟩
      have h := hu _ _ (ei.trans ej.symm)
      rwa [i.encode_at_u A _ ⟨x,hi⟩ ei,j.encode_at_u B _ ⟨x,hj⟩ ej] at h
    · intro y hi hj
      have ei := i.positionV_eq ⟨y,hi⟩
      have ej := j.positionV_eq ⟨y,hj⟩
      have h := hv _ _ (ei.trans ej.symm)
      rwa [i.encode_at_v A _ ⟨y,hi⟩ ei,j.encode_at_v B _ ⟨y,hj⟩ ej] at h
    · intro c hi hj
      have ei := i.positionU_eq ⟨Φ.left c,hi⟩
      have ej := j.positionV_eq ⟨Φ.right c,hj⟩
      have h := hc c _ _ ei.symm ej.symm
      rwa [i.encode_at_u A _ ⟨Φ.left c,hi⟩ ei,j.encode_at_v B _ ⟨Φ.right c,hj⟩ ej] at h
  · rintro ⟨hu,hv,hc⟩
    refine ⟨?_,?_,?_⟩
    · intro k l h
      have hi : i.2.1 k ∈ i.scopeU := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
      have hj : i.2.1 k ∈ j.scopeU := Finset.mem_image.mpr ⟨l,Finset.mem_univ _,h.symm⟩
      rw [i.encode_at_u A k ⟨_,hi⟩ rfl,j.encode_at_u B l ⟨_,hj⟩ h.symm]
      exact hu _ hi hj
    · intro k l h
      have hi : i.2.2 k ∈ i.scopeV := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
      have hj : i.2.2 k ∈ j.scopeV := Finset.mem_image.mpr ⟨l,Finset.mem_univ _,h.symm⟩
      rw [i.encode_at_v A k ⟨_,hi⟩ rfl,j.encode_at_v B l ⟨_,hj⟩ h.symm]
      exact hv _ hi hj
    · intro c k l hx hy
      have hi : Φ.left c ∈ i.scopeU := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,hx.symm⟩
      have hj : Φ.right c ∈ j.scopeV := Finset.mem_image.mpr ⟨l,Finset.mem_univ _,hy.symm⟩
      rw [i.encode_at_u A k ⟨_,hi⟩ hx.symm,j.encode_at_v B l ⟨_,hj⟩ hy.symm]
      exact hc c hi hj
end VertexCover.LabelCover.Query

namespace VertexCover.LabelCover
 theorem compatible_pair_iff (Φ : LabelCover) {d : ℕ} (I : Finset (Φ.Coordinate d)) :
    Φ.Compatible I ↔
      (∀ p ∈ I, ∀ q ∈ I, p.1=q.1 → p=q) ∧
      (∀ p ∈ I, ∀ q ∈ I, Query.LabelPair p.1 q.1 p.2 q.2) := by
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨h₁,fun p hp q hq => ⟨h₂ p hp q hq,h₃ p hp q hq,h₄ p hp q hq⟩⟩
  · rintro ⟨h₁,h⟩
    exact ⟨h₁,fun p hp q hq => (h p hp q hq).1,
      fun p hp q hq => (h p hp q hq).2.1,fun p hp q hq => (h p hp q hq).2.2⟩
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
