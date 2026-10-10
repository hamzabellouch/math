import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.RelativeClearing
variable {k A B R : Type*} [CommRing k] [CommRing A] [IsDomain A] [CommRing B] [CommRing R]
  [Algebra k A] [Algebra k B] [Algebra k R]
variable (h : A →ₐ[k] B) (f : B →ₐ[k] R) (D : Derivation k A A)
def subalgebra : Subalgebra k R where
  carrier := {r | ∃ c : A, ∃ b : B, D c=0 ∧ c≠0 ∧ f (h c)*r=f b}
  algebraMap_mem' a := ⟨1,algebraMap k B a,D.map_one_eq_zero,one_ne_zero,by simp⟩
  add_mem' := by
    rintro r s ⟨c,b,hc,hcn,hcb⟩ ⟨d,e,hd,hdn,hde⟩
    refine ⟨c*d,h d*b+h c*e,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · simp only [map_mul,map_add]
      calc f (h c)*f (h d)*(r+s)=f (h d)*(f (h c)*r)+f (h c)*(f (h d)*s) := by ring
        _ = _ := by rw [hcb,hde]
  mul_mem' := by
    rintro r s ⟨c,b,hc,hcn,hcb⟩ ⟨d,e,hd,hdn,hde⟩
    refine ⟨c*d,b*e,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · simp only [map_mul]
      calc f (h c)*f (h d)*(r*s)=(f (h c)*r)*(f (h d)*s) := by ring
        _ = _ := by rw [hcb,hde]
lemma image_mem (b : B) : f b ∈ subalgebra h f D := ⟨1,b,D.map_one_eq_zero,one_ne_zero,by simp⟩
lemma uniform (s : Finset B) (E : Derivation k R R)
    (hc : ∀ b, E (f b) ∈ subalgebra h f D) :
    ∃ c : A, D c=0 ∧ c≠0 ∧ ∀ b∈s, ∃ t : B, f (h c)*E (f b)=f t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,D.map_one_eq_zero,one_ne_zero,by simp⟩
  | @insert b s hbs ih =>
    obtain ⟨c,t,hc,hcn,hct⟩ := hc b
    obtain ⟨d,hd,hdn,hds⟩ := ih
    refine ⟨c*d,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl|ha
      · refine ⟨h d*t,?_⟩
        simp only [map_mul]
        calc f (h c)*f (h d)*E (f a)=f (h d)*(f (h c)*E (f a)) := by ring
          _ = _ := by rw [hct]
      · obtain ⟨u,hu⟩ := hds a ha
        refine ⟨h c*u,?_⟩
        simp only [map_mul]
        rw [mul_assoc,hu]
end ComplexCancellation.RelativeClearing

namespace ComplexCancellation.DerivationRange
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R] [Algebra k B] [Algebra k R]
def stable (f : B →ₐ[k] R) (E : Derivation k R R) : Subalgebra k B where
  carrier := {b | ∃ t : B, E (f b)=f t}
  algebraMap_mem' a := ⟨0,by rw [f.commutes,E.map_algebraMap,map_zero]⟩
  add_mem' := by
    rintro r s ⟨t,ht⟩ ⟨u,hu⟩
    exact ⟨t+u,by rw [map_add,map_add,ht,hu,map_add]⟩
  mul_mem' := by
    rintro r s ⟨t,ht⟩ ⟨u,hu⟩
    exact ⟨r*u+s*t,by rw [map_mul,Derivation.leibniz,ht,hu,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul]⟩
lemma stable_of_generators (f : B →ₐ[k] R) (E : Derivation k R R) (s : Set B)
    (hs : Algebra.adjoin k s=⊤) (he : ∀ b∈s, ∃ t, E (f b)=f t) : ∀ b, ∃ t, E (f b)=f t := by
  have h : Algebra.adjoin k s ≤ stable f E := Algebra.adjoin_le he
  rw [hs] at h
  exact fun b => h (show b∈(⊤ : Subalgebra k B) from trivial)
end ComplexCancellation.DerivationRange

end

end OAI
