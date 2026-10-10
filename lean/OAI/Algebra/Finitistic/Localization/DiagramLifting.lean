import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Linear.LinearFunctor

namespace OAI
namespace LittleFinitistic.DiagramLifting
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D]
variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
variable [W.HasRightCalculusOfFractions]

/-- Finitely many localized arrows admit one common source denominator. -/
theorem finite_roof (n : ℕ) (X : C) (Y : Fin n → C)
    (f : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (Z : C) (u : Z ⟶ X), W u ∧
      ∃ (g : ∀ i, Z ⟶ Y i), ∀ i, L.map u ≫ f i = L.map (g i) := by
  induction n generalizing X with
  | zero => exact ⟨X,𝟙 X,W.id_mem X,(fun i => Fin.elim0 i),fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨φ,hφ⟩ := Localization.exists_rightFraction L W (f 0)
    obtain ⟨Z,u,hu,g,hg⟩ := ih φ.X' (fun i => Y i.succ)
      (fun i => L.map φ.s ≫ f i.succ)
    refine ⟨Z,u ≫ φ.s,W.comp_mem _ _ hu φ.hs,Fin.cases (u ≫ φ.f) g,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero,Functor.map_comp,assoc,hφ,φ.map_s_comp_map]
    · simpa only [Fin.cases_succ,Functor.map_comp,assoc] using hg j

section Zero
variable [HasZeroMorphisms C] [HasZeroMorphisms D] [L.PreservesZeroMorphisms]

/-- A finite family vanishing after localization is annihilated by one source denominator. -/
theorem finite_zero_refinement (n : ℕ) (X : C) (Y : Fin n → C)
    (f : ∀ i, X ⟶ Y i) (hf : ∀ i, L.map (f i) = 0) :
    ∃ (Z : C) (u : Z ⟶ X), W u ∧ ∀ i, u ≫ f i = 0 := by
  induction n generalizing X with
  | zero => exact ⟨X,𝟙 X,W.id_mem X,fun i => Fin.elim0 i⟩
  | succ n ih =>
    have h0 : L.map (f 0) = L.map (0 : X ⟶ Y 0) := by simpa using hf 0
    obtain ⟨X',u,hu,he⟩ := (MorphismProperty.map_eq_iff_precomp L W (f 0) 0).mp h0
    have he0 : u ≫ f 0 = 0 := by simpa using he
    obtain ⟨Z,v,hv,hg⟩ := ih X' (fun i => Y i.succ) (fun i => u ≫ f i.succ)
      (fun i => by simp [hf])
    refine ⟨Z,v ≫ u,W.comp_mem _ _ hv hu,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [assoc,he0]
    · simpa only [assoc] using hg j

end Zero

open scoped BigOperators
variable {k : Type*} [CommRing k] [Preadditive C] [Preadditive D]
variable [Linear k C] [Linear k D] [L.Additive] [L.Linear k]

/-- A finite three-vertex diagram with arbitrary homogeneous quadratic relations
lifts along a right-fraction localization. The displayed denominator maps give
an isomorphism from the localized lift to the original entire diagram. -/
theorem quadratic_diagram_lift (na nb nr : ℕ) (X₀ X₁ X₂ : C)
    (a : Fin na → (L.obj X₀ ⟶ L.obj X₁))
    (b : Fin nb → (L.obj X₁ ⟶ L.obj X₂))
    (r : Fin nr → Fin na → Fin nb → k)
    (hr : ∀ ρ, ∑ i, ∑ j, r ρ i j • (a i ≫ b j) = 0) :
    ∃ (D₀ D₁ : C) (u₀ : D₀ ⟶ X₀) (u₁ : D₁ ⟶ X₁), W u₀ ∧ W u₁ ∧
    ∃ (f : Fin na → (D₀ ⟶ D₁)) (g : Fin nb → (D₁ ⟶ X₂)),
      (∀ i, L.map u₀ ≫ a i = L.map (f i) ≫ L.map u₁) ∧
      (∀ j, L.map u₁ ≫ b j = L.map (g j)) ∧
      (∀ ρ, ∑ i, ∑ j, r ρ i j • (f i ≫ g j) = 0) := by
  classical
  obtain ⟨D₁,u₁,hu₁,g,hg⟩ := finite_roof L W nb X₁ (fun _ => X₂) b
  have : IsIso (L.map u₁) := Localization.inverts L W _ hu₁
  obtain ⟨D₀,u₀,hu₀,f,hf⟩ := finite_roof L W na X₀ (fun _ => D₁)
    (fun i => a i ≫ inv (L.map u₁))
  have hpath (i : Fin na) (j : Fin nb) :
      L.map (f i ≫ g j) = L.map u₀ ≫ (a i ≫ b j) := by
    rw [Functor.map_comp,← hf i,← hg j]
    simp only [assoc,IsIso.inv_hom_id_assoc]
  let relations : Fin nr → (D₀ ⟶ X₂) := fun ρ => ∑ i, ∑ j, r ρ i j • (f i ≫ g j)
  have hrel (ρ : Fin nr) : L.map (relations ρ) = 0 := by
    dsimp [relations]
    simp only [Functor.map_sum,Functor.map_smul,hpath]
    have h := congrArg (fun t => L.map u₀ ≫ t) (hr ρ)
    simpa only [Preadditive.comp_sum,Linear.comp_smul,comp_zero] using h
  obtain ⟨D₀',v,hv,hvrel⟩ := finite_zero_refinement L W nr D₀ (fun _ => X₂) relations hrel
  refine ⟨D₀',D₁,v ≫ u₀,u₁,W.comp_mem _ _ hv hu₀,hu₁,
    (fun i => v ≫ f i),g,?_,hg,?_⟩
  · intro i
    have hi := congrArg (fun t => t ≫ L.map u₁) (hf i)
    simp only [assoc,IsIso.inv_hom_id,comp_id] at hi
    simp only [Functor.map_comp,assoc]
    rw [← hi]
  · intro ρ
    have h := hvrel ρ
    dsimp [relations] at h
    simpa only [Preadditive.comp_sum,Linear.comp_smul,assoc] using h

include W in
/-- Every finite three-level quadratic diagram in the localized category,
including objects not literally presented as functor images, has an isomorphic lift. -/
theorem finite_quadratic_diagram_lifting (na nb nr : ℕ) (Y₀ Y₁ Y₂ : D)
    (a : Fin na → (Y₀ ⟶ Y₁)) (b : Fin nb → (Y₁ ⟶ Y₂))
    (r : Fin nr → Fin na → Fin nb → k)
    (hr : ∀ ρ, ∑ i, ∑ j, r ρ i j • (a i ≫ b j) = 0) :
    ∃ (X₀ X₁ X₂ : C) (e₀ : L.obj X₀ ≅ Y₀) (e₁ : L.obj X₁ ≅ Y₁)
      (e₂ : L.obj X₂ ≅ Y₂) (f : Fin na → (X₀ ⟶ X₁)) (g : Fin nb → (X₁ ⟶ X₂)),
      (∀ i, L.map (f i) ≫ e₁.hom = e₀.hom ≫ a i) ∧
      (∀ j, L.map (g j) ≫ e₂.hom = e₁.hom ≫ b j) ∧
      (∀ ρ, ∑ i, ∑ j, r ρ i j • (f i ≫ g j) = 0) := by
  classical
  have := Localization.essSurj L W
  let X₀ := L.objPreimage Y₀
  let X₁ := L.objPreimage Y₁
  let X₂ := L.objPreimage Y₂
  let e₀ : L.obj X₀ ≅ Y₀ := L.objObjPreimageIso Y₀
  let e₁ : L.obj X₁ ≅ Y₁ := L.objObjPreimageIso Y₁
  let e₂ : L.obj X₂ ≅ Y₂ := L.objObjPreimageIso Y₂
  let a' := fun i => e₀.hom ≫ a i ≫ e₁.inv
  let b' := fun j => e₁.hom ≫ b j ≫ e₂.inv
  have hr' (ρ : Fin nr) : ∑ i, ∑ j, r ρ i j • (a' i ≫ b' j) = 0 := by
    dsimp [a',b']
    simp only [assoc,Iso.inv_hom_id_assoc]
    have h := congrArg (fun t => e₀.hom ≫ t ≫ e₂.inv) (hr ρ)
    simpa only [Preadditive.comp_sum,Preadditive.sum_comp,Linear.comp_smul,
      Linear.smul_comp,assoc,comp_zero,zero_comp] using h
  obtain ⟨D₀,D₁,u₀,u₁,hu₀,hu₁,f,g,hf,hg,hrel⟩ :=
    quadratic_diagram_lift L W na nb nr X₀ X₁ X₂ a' b' r hr'
  refine ⟨D₀,D₁,X₂,(Localization.isoOfHom L W u₀ hu₀) ≪≫ e₀,
    (Localization.isoOfHom L W u₁ hu₁) ≪≫ e₁,e₂,f,g,?_,?_,hrel⟩
  · intro i
    have h := congrArg (fun t => t ≫ e₁.hom) (hf i)
    simpa only [a',Iso.trans_hom,Localization.isoOfHom_hom,assoc,
      Iso.inv_hom_id,comp_id] using h.symm
  · intro j
    have h := congrArg (fun t => t ≫ e₂.hom) (hg j)
    simpa only [b',Iso.trans_hom,Localization.isoOfHom_hom,assoc,
      Iso.inv_hom_id,comp_id] using h.symm
end LittleFinitistic.DiagramLifting

end OAI
