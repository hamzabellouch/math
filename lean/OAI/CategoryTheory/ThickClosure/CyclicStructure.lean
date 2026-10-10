import OAI.CategoryTheory.ThickClosure.DerivedHom

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.CyclicStructure
section ShiftStructure
open CategoryTheory CategoryTheory.Limits
universe u v w v'
variable {C : Type u} [Category.{v} C] {E : Type w} [Category.{v'} E]

noncomputable def initial_map (W : MorphismProperty C) (L : C ⥤ E) [L.IsLocalization W]
    {Z : C} (hZ : IsInitial Z) : IsInitial (L.obj Z) := by
  letI : L.EssSurj := Localization.essSurj L W
  have h : W.IsInvertedBy (coyoneda.obj (Opposite.op Z)) := by
    intro A B f hf
    rw [CategoryTheory.isIso_iff_bijective]
    exact ⟨fun _ _ _ => hZ.hom_ext _ _, fun g => ⟨hZ.to _, hZ.hom_ext _ _⟩⟩
  refine IsInitial.ofUniqueHom (fun X => L.map (hZ.to (L.objPreimage X)) ≫
    (L.objObjPreimageIso X).hom) ?_
  intro X f
  apply (cancel_mono (L.objObjPreimageIso X).inv).mp
  obtain ⟨a, ha⟩ := (HahnWilson.LocalizationHom.map_bijective_of_inverts C E W L
    Z (L.objPreimage X) h).2 (f ≫ (L.objObjPreimageIso X).inv)
  rw [← ha]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg L.map (hZ.hom_ext _ _)

theorem isZero_map (W : MorphismProperty C) (L : C ⥤ E) [L.IsLocalization W]
    {Z : C} (hZ : IsZero Z) : IsZero (L.obj Z) := by
  have hi := initial_map W L hZ.isInitial
  have ht := initial_map W.op L.op hZ.op.isInitial
  exact ⟨fun X => ⟨⟨⟨hi.to X⟩, fun f => hi.hom_ext f _⟩⟩,
    fun X => ⟨⟨⟨ht.unop.from X⟩, fun f => ht.unop.hom_ext f _⟩⟩⟩

variable (R : Type u) [Ring R] (D : ℕ)

theorem quasiIso_products :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).IsStableUnderFiniteProducts := by
  constructor
  intro J hJ
  apply MorphismProperty.IsStableUnderProductsOfShape.mk
  intro X₁ X₂ _ _ f hf
  rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D)) i
  have hn : H.map (Limits.Pi.map f) ≫ piComparison H X₂ =
      piComparison H X₁ ≫ Limits.Pi.map (fun j => H.map (f j)) := by
    apply Limits.Pi.hom_ext
    intro j
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
    rw [← H.map_comp, Limits.Pi.map_π, H.map_comp, ← Category.assoc, piComparison_comp_π]
  have (j : J) : QuasiIso (f j) := hf j
  have (j : J) : IsIso (H.map (f j)) := inferInstanceAs (IsIso (HomologicalComplex.homologyMap (f j) i))
  have : IsIso (H.map (Limits.Pi.map f) ≫ piComparison H X₂) := by rw [hn]; infer_instance
  exact (isIso_comp_right_iff (H.map (Limits.Pi.map f)) (piComparison H X₂)).mp inferInstance

end ShiftStructure

open CategoryTheory CategoryTheory.Limits
open HahnWilson.PeriodicDerived ZeroObject
universe u w
variable (R : Type u) [Ring R] (D : ℕ)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

noncomputable instance : HasZeroObject (PeriodicDerived.{u,w} R D) :=
  ⟨⟨(Q.{u,w} R D).obj 0, isZero_map (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))) (Q.{u,w} R D) (isZero_zero _)⟩⟩

noncomputable instance : HasZeroMorphisms (PeriodicDerived.{u,w} R D) :=
  (isZero_zero (PeriodicDerived.{u,w} R D)).hasZeroMorphisms

instance : (Q.{u,w} R D).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_map_zero_object
    ((isZero_map (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))) (Q.{u,w} R D) (isZero_zero _)).iso (isZero_zero _))

instance : (HomologicalComplex.quasiIso (ModuleCat.{u} R)
    (.down (ZMod D))).IsStableUnderFiniteProducts := quasiIso_products R D

omit [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}] in
theorem complexFiniteProducts : HasFiniteProducts (PeriodicComplex R D) := by
  constructor
  intro n
  let : HasLimitsOfShape (Discrete (Fin n)) (ModuleCat.{u} R) :=
    ModuleCat.hasLimitsOfShape.{0,0,u,u}
  exact HomologicalComplex.instHasLimitsOfShape

noncomputable instance : HasFiniteProducts (PeriodicDerived.{u,w} R D) := by
  let := complexFiniteProducts R D
  change HasFiniteProducts ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).Localization')
  infer_instance

instance : PreservesFiniteProducts (Q.{u,w} R D) := by
  let := complexFiniteProducts R D
  change PreservesFiniteProducts ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).Q')
  infer_instance

end HahnWilson.CyclicStructure

end

end OAI
