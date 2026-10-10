import Mathlib

namespace OAI

open CategoryTheory CategoryTheory.Limits
namespace FiberFunctorProof
universe v u
noncomputable section
variable {C : Type u} [Category.{v} C] [Abelian C]

 

lemma separator_of_projective_weak_generator (P : C) [Projective P]
    (hP : ∀ X : C, ¬ IsZero X → ∃ f : P ⟶ X, f ≠ 0) : IsSeparator P := by
  apply (Preadditive.isSeparator_iff P).2
  intro X Y f hf
  by_contra hn
  have hI : ¬ IsZero (image f) := by
    intro hz
    apply hn
    rw [← image.fac f]
    simpa using congrArg (fun g => factorThruImage f ≫ g) (hz.eq_of_src (image.ι f) 0)
  obtain ⟨a,ha⟩ := hP (image f) hI
  let b := Projective.factorThru a (factorThruImage f)
  have hb : b ≫ factorThruImage f = a := Projective.factorThru_comp _ _
  apply ha
  apply (cancel_mono (image.ι f)).1
  calc
    a ≫ image.ι f = b ≫ f := by rw [← hb, Category.assoc, image.fac]
    _ = 0 := hf b
    _ = 0 ≫ image.ι f := by simp

 

theorem finite_projective_separator
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughProjectives C]
    (hA : ∀ X : C, IsArtinianObject X)
    (hS : ∃ (m : ℕ) (S : Fin m → C),
      (∀ i, Simple (S i)) ∧ ∀ X : C, Simple X → ∃ i, Nonempty (S i ≅ X)) :
    ∃ P : C, Projective P ∧ IsSeparator P := by
  classical
  obtain ⟨m,S,hS,hrep⟩ := hS
  let J := ULift.{v} (Fin m)
  let Q : J → C := fun i => Projective.over (S i.down)
  let : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  let P := ⨁ Q
  have hproj : Projective P := inferInstance
  refine ⟨P,hproj,separator_of_projective_weak_generator P ?_⟩
  intro X hX
  let := hA X
  obtain ⟨T,hT⟩ := exists_simple_subobject hX
  obtain ⟨i,⟨e⟩⟩ := hrep (T : C) hT
  let a : Q ⟨i⟩ ⟶ X := Projective.π (S i) ≫ e.hom ≫ T.arrow
  have ha : a ≠ 0 := by
    intro hz
    have ht : e.hom ≫ T.arrow = 0 := (cancel_epi (Projective.π (S i))).1
      (by simpa [a] using hz)
    have hzT : IsZero (T : C) := IsZero.of_mono_eq_zero T.arrow
      ((cancel_epi e.hom).1 (by simpa using ht))
    exact (Simple.not_isZero (T : C)) hzT
  refine ⟨biproduct.π Q ⟨i⟩ ≫ a, ?_⟩
  intro hz
  apply ha
  have he := congrArg (fun f => biproduct.ι Q ⟨i⟩ ≫ f) hz
  simpa using he

local instance : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts

 

theorem finite_sum_surjection (k : Type*) [Field k] [Linear k C]
    (P X : C) (hP : IsSeparator P) [Module.Finite k (P ⟶ X)] :
    ∃ (n : ℕ) (e : (⨁ fun _ : Fin n => P) ⟶ X), Epi e := by
  classical
  let b := Module.finBasis k (P ⟶ X)
  let e : (⨁ fun _ : Fin (Module.finrank k (P ⟶ X)) => P) ⟶ X := biproduct.desc b
  refine ⟨_, e, ?_⟩
  apply Abelian.epi_of_cokernel_π_eq_zero
  apply (Preadditive.isSeparator_iff P).1 hP
  intro a
  have hL : Linear.rightComp k P (cokernel.π e) = 0 := by
    apply b.ext
    intro i
    change b i ≫ cokernel.π e = 0
    have h := congrArg (fun f => biproduct.ι (fun _ : Fin (Module.finrank k (P ⟶ X)) => P) i ≫ f)
      (cokernel.condition e)
    simpa only [e, ← Category.assoc, biproduct.ι_desc, Limits.comp_zero] using h
  exact congrArg (fun L : (P ⟶ X) →ₗ[k] (P ⟶ cokernel e) => L a) hL
end
end FiberFunctorProof

end OAI
