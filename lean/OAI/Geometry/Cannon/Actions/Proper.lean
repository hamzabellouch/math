import Mathlib

namespace OAI

/-! Properness and cocompactness transferred through equivariant maps. -/

section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonActions
open Set

variable {Γ X Y : Type*} [Group Γ] [TopologicalSpace X] [TopologicalSpace Y]

def Proper (A : Γ →* (X ≃ₜ X)) : Prop :=
  ∀ K : Set X, IsCompact K → {g : Γ | ∃ x ∈ K, A g x ∈ K}.Finite

def Cocompact (A : Γ →* (X ≃ₜ X)) : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : Γ, ∃ y ∈ K, A g y=x

theorem proper_descends {A : Γ →* (X ≃ₜ X)} {B : Γ →* (Y ≃ₜ Y)}
    {p : X → Y} (hp : IsProperMap p) (hs : Function.Surjective p)
    (he : ∀ g x, p (A g x)=B g (p x)) (hA : Proper A) : Proper B := by
  intro K hK
  apply (hA (p ⁻¹' K) (hp.isCompact_preimage hK)).subset
  rintro g ⟨y,hy,hgy⟩
  obtain ⟨x,rfl⟩ := hs y
  exact ⟨x,hy,by simpa only [mem_preimage,he] using hgy⟩

theorem cocompact_descends {A : Γ →* (X ≃ₜ X)} {B : Γ →* (Y ≃ₜ Y)}
    {p : X → Y} (hp : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g x, p (A g x)=B g (p x)) (hA : Cocompact A) : Cocompact B := by
  obtain ⟨K,hK,hAK⟩ := hA
  refine ⟨p '' K,hK.image hp,?_⟩
  intro y
  obtain ⟨x,rfl⟩ := hs y
  obtain ⟨g,z,hz,rfl⟩ := hAK x
  exact ⟨g,p z,mem_image_of_mem p hz,(he g z).symm⟩

theorem proper_finite_kernel [Nonempty X] {A : Γ →* (X ≃ₜ X)} (hA : Proper A) :
    (A.ker : Set Γ).Finite := by
  obtain ⟨x⟩ := ‹Nonempty X›
  apply (hA {x} isCompact_singleton).subset
  intro g hg
  have hh : A g=1 := hg
  exact ⟨x,mem_singleton x,by simp only [hh,Homeomorph.one_apply,mem_singleton_iff]⟩

def conjugate (ψ : X ≃ₜ Y) (A : Γ →* (X ≃ₜ X)) : Γ →* (Y ≃ₜ Y) where
  toFun g := (ψ.symm.trans (A g)).trans ψ
  map_one' := by
    ext y
    simp only [map_one,Homeomorph.trans_apply,Homeomorph.one_apply,Homeomorph.apply_symm_apply]
  map_mul' g h := by
    ext y
    simp only [map_mul,Homeomorph.trans_apply,Homeomorph.mul_apply,Homeomorph.symm_apply_apply]

lemma conjugate_equivariant (ψ : X ≃ₜ Y) (A : Γ →* (X ≃ₜ X)) (g : Γ) (x : X) :
    ψ (A g x)=conjugate ψ A g (ψ x) := by
  change ψ (A g x)=ψ (A g (ψ.symm (ψ x)))
  rw [ψ.symm_apply_apply]

theorem proper_conjugate (ψ : X ≃ₜ Y) {A : Γ →* (X ≃ₜ X)} (hA : Proper A) :
    Proper (conjugate ψ A) :=
  proper_descends ψ.isProperMap ψ.surjective (conjugate_equivariant ψ A) hA

theorem cocompact_conjugate (ψ : X ≃ₜ Y) {A : Γ →* (X ≃ₜ X)} (hA : Cocompact A) :
    Cocompact (conjugate ψ A) :=
  cocompact_descends ψ.continuous ψ.surjective (conjugate_equivariant ψ A) hA

end CannonActions

namespace CannonActions
open Set

variable {X Y Z Γ : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [Group Γ]
abbrev OrderedTriples (X : Type*) := {t : Fin 3 → X // Function.Injective t}
def triplesMap (f : X ≃ₜ Y) (t : OrderedTriples X) : OrderedTriples Y :=
  ⟨f ∘ t.val,f.injective.comp t.property⟩
lemma continuous_triplesMap (f : X ≃ₜ Y) : Continuous (triplesMap f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact f.continuous.comp ((continuous_apply i).comp continuous_subtype_val)
def triplesCongr (f : X ≃ₜ Y) : OrderedTriples X ≃ₜ OrderedTriples Y where
  toFun := triplesMap f
  invFun := triplesMap f.symm
  left_inv t := by apply Subtype.ext; funext i; exact f.symm_apply_apply _
  right_inv t := by apply Subtype.ext; funext i; exact f.apply_symm_apply _
  continuous_toFun := continuous_triplesMap f
  continuous_invFun := continuous_triplesMap f.symm

def triplesHom : (X ≃ₜ X) →* (OrderedTriples X ≃ₜ OrderedTriples X) where
  toFun := triplesCongr
  map_one' := by apply Homeomorph.ext; intro t; rfl
  map_mul' f g := by apply Homeomorph.ext; intro t; rfl

def triplesAction (A : Γ →* (X ≃ₜ X)) : Γ →* (OrderedTriples X ≃ₜ OrderedTriples X) := triplesHom.comp A

lemma triples_conjugate (A : Γ →* (X ≃ₜ X)) (ψ : X ≃ₜ Y) :
    triplesAction (conjugate ψ A)=conjugate (triplesCongr ψ) (triplesAction A) := by
  apply MonoidHom.ext
  intro g
  apply Homeomorph.ext
  intro t
  rfl
end CannonActions

end
end
end
end
end
end

end OAI
