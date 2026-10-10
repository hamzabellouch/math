import Mathlib

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y Z : Scheme.{u}}
def O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def endValue (f : O X ⟶ O X) : Γ(X, ⊤) := f.app ⊤ (1 : Γ(X, ⊤))

lemma end_apply (f : O X ⟶ O X) (U : X.Opens) (a : Γ(X, U)) :
    f.app U a = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) := by
  have h := f.app_smul (r := a) (x := (1 : Γ(X, U)))
  change f.app U (a * 1 : Γ(X, U)) = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) at h
  simpa only [mul_one] using h

@[simp] lemma endValue_id : endValue (𝟙 (O X)) = 1 := rfl

lemma endValue_comp (f g : O X ⟶ O X) :
    endValue (f ≫ g) = endValue f * endValue g := by
  exact end_apply g ⊤ (endValue f)

def frameChange {M : X.Modules} (e f : M ≅ O X) : Γ(X, ⊤)ˣ where
  val := endValue (e.inv ≫ f.hom)
  inv := endValue (f.inv ≫ e.hom)
  val_inv := by rw [← endValue_comp]; simp
  inv_val := by rw [← endValue_comp]; simp

def coefficient {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) : Γ(X, ⊤) :=
  endValue (s ≫ e.hom)

lemma coefficient_change {M : X.Modules} (e f : M ≅ O X) (s : O X ⟶ M) :
    coefficient f s = (frameChange e f : Γ(X, ⊤)) * coefficient e s := by
  change endValue (s ≫ f.hom) = endValue (e.inv ≫ f.hom) * endValue (s ≫ e.hom)
  rw [mul_comm, ← endValue_comp]
  simp

lemma coefficient_frame {M : X.Modules} (e : M ≅ O X) : coefficient e e.inv = 1 := by
  simp [coefficient]

def restrictSection (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (s : O X ⟶ M) : O Y ⟶ M.restrict φ :=
  (Scheme.Modules.restrictUnitIso φ).inv ≫ (Scheme.Modules.restrictFunctor φ).map s

def restrictFrame (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) : M.restrict φ ≅ O Y :=
  (Scheme.Modules.restrictFunctor φ).mapIso e ≪≫ Scheme.Modules.restrictUnitIso φ

lemma end_naturality (f : O X ⟶ O X) (U : X.Opens) :
    f.app U (1 : Γ(X, U)) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change f.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) at h
  simpa only [map_one] using h

lemma endValue_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] (f : O X ⟶ O X) :
    endValue (restrictSection φ f ≫ (Scheme.Modules.restrictUnitIso φ).hom) =
      φ.appTop (endValue f) := by
  change (φ.appIso ⊤).hom (f.app (φ ''ᵁ ⊤) ((φ.appIso ⊤).inv 1)) = _
  rw [map_one, end_naturality]
  change (X.presheaf.map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
    (φ.appIso ⊤).hom) (endValue f) = _
  rw [Scheme.Hom.appIso_hom']
  simp only [Scheme.Hom.appTop, Scheme.Hom.appLE,
    Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  congr 1
  rw [show ((Opens.map φ.base).map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op.unop).op ≫
      (homOfLE (show (⊤ : Y.Opens) ≤ φ ⁻¹ᵁ (φ ''ᵁ ⊤) from by intro x _; exact ⟨x, Set.mem_univ _, rfl⟩)).op = 𝟙 _ from Subsingleton.elim _ _]
  change ConcreteCategory.hom (φ.app ⊤ ≫ Y.presheaf.map (𝟙 (Opposite.op ⊤))) =
    ConcreteCategory.hom (φ.app ⊤)
  exact congrArg ConcreteCategory.hom
    ((congrArg (fun morphism => φ.app ⊤ ≫ morphism) (Y.presheaf.map_id _)).trans
      (Category.comp_id _))

lemma coefficient_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (restrictFrame φ e) (restrictSection φ s) = φ.appTop (coefficient e s) := by
  let restriction := Scheme.Modules.restrictFunctor φ
  let unitIso := Scheme.Modules.restrictUnitIso φ
  have composition :
      (unitIso.inv ≫ restriction.map s) ≫ restriction.map e.hom ≫ unitIso.hom =
        (unitIso.inv ≫ restriction.map (s ≫ e.hom)) ≫ unitIso.hom := by
    calc
      _ = unitIso.inv ≫ (restriction.map s ≫ restriction.map e.hom) ≫ unitIso.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun morphism => unitIso.inv ≫ morphism)
            (Category.assoc _ _ _).symm)
      _ = unitIso.inv ≫ restriction.map (s ≫ e.hom) ≫ unitIso.hom :=
        congrArg (fun morphism => unitIso.inv ≫ morphism ≫ unitIso.hom)
          (restriction.map_comp s e.hom).symm
      _ = _ := (Category.assoc _ _ _).symm
  exact (congrArg endValue composition).trans (endValue_restrict φ (s ≫ e.hom))

lemma restrictUnit_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] :
    (Scheme.Modules.restrictUnitIso (φ ≫ ψ)).inv ≫
      (Scheme.Modules.restrictFunctorComp φ ψ).hom.app (O Z) =
    (Scheme.Modules.restrictUnitIso φ).inv ≫
      (Scheme.Modules.restrictFunctor φ).map (Scheme.Modules.restrictUnitIso ψ).inv := by
  ext U a
  change Z.presheaf.map (eqToHom (show ψ ''ᵁ (φ ''ᵁ U) = (φ ≫ ψ) ''ᵁ U from by simp)).op
    ((φ ≫ ψ).appIso U |>.inv |>.hom |>.toFun <| a) =
      (ψ.appIso (φ ''ᵁ U)).inv ((φ.appIso U).inv a)
  rw [Scheme.Hom.comp_appIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv]
  change ( (φ.appIso U).inv ≫ (ψ.appIso (φ ''ᵁ U)).inv ≫
    Z.presheaf.map _ ≫ Z.presheaf.map _) a = _
  rw [← CategoryTheory.Functor.map_comp]
  simp
  rfl

lemma restrictSection_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules} (s : O Z ⟶ M) :
    restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M =
      restrictSection φ (restrictSection ψ s) := by
  let first := Scheme.Modules.restrictFunctor φ
  let second := Scheme.Modules.restrictFunctor ψ
  let combined := Scheme.Modules.restrictFunctor (φ ≫ ψ)
  let comparison := (Scheme.Modules.restrictFunctorComp φ ψ).hom
  let unitIso := Scheme.Modules.restrictUnitIso (φ ≫ ψ)
  calc
    _ = unitIso.inv ≫ combined.map s ≫ comparison.app M := Category.assoc _ _ _
    _ = unitIso.inv ≫ comparison.app (O Z) ≫ (second ⋙ first).map s :=
      congrArg (fun morphism => unitIso.inv ≫ morphism) (comparison.naturality s)
    _ = (unitIso.inv ≫ comparison.app (O Z)) ≫ (second ⋙ first).map s :=
      (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.restrictUnitIso φ).inv ≫
        first.map (Scheme.Modules.restrictUnitIso ψ).inv) ≫ (second ⋙ first).map s :=
      congrArg (fun morphism => morphism ≫ (second ⋙ first).map s)
        (restrictUnit_comp φ ψ)
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun morphism => (Scheme.Modules.restrictUnitIso φ).inv ≫ morphism)
        (first.map_comp (Scheme.Modules.restrictUnitIso ψ).inv (second.map s)).symm)

lemma coefficient_transport {M N : X.Modules} (e : M ≅ N) (f : N ≅ O X)
    (s : O X ⟶ M) : coefficient (e ≪≫ f) s = coefficient f (s ≫ e.hom) := by
  simp only [coefficient, Iso.trans_hom, Category.assoc]

lemma coefficient_restrict_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules}
    (e : M.restrict ψ ≅ O X) (s : O Z ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctorComp φ ψ).app M ≪≫ restrictFrame φ e)
      (restrictSection (φ ≫ ψ) s) = φ.appTop (coefficient e (restrictSection ψ s)) := by
  rw [coefficient_transport]
  change coefficient (restrictFrame φ e)
    (restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M) = _
  rw [restrictSection_comp, coefficient_restrict]

lemma restrictSection_congr {φ ψ : Y ⟶ X} (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : X.Modules} (s : O X ⟶ M) :
    restrictSection φ s ≫ (Scheme.Modules.restrictFunctorCongr h).hom.app M =
      restrictSection ψ s := by
  subst ψ
  have H : (Scheme.Modules.restrictFunctorCongr (show φ = φ from rfl)).hom.app M = 𝟙 _ := by
    ext U a
    simp
    rfl
  rw [H, Category.comp_id]

lemma overlap_coefficients {W : Scheme.{u}} (φ : Y ⟶ X) (ψ : Z ⟶ X)
    (a : W ⟶ Y) (b : W ⟶ Z) [IsOpenImmersion φ] [IsOpenImmersion ψ]
    [IsOpenImmersion a] [IsOpenImmersion b] (h : a ≫ φ = b ≫ ψ)
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (f : M.restrict ψ ≅ O Z) :
    ∃ c : Γ(W, ⊤)ˣ, ∀ s : O X ⟶ M,
      b.appTop (coefficient f (restrictSection ψ s)) =
      (c : Γ(W, ⊤)) * a.appTop (coefficient e (restrictSection φ s)) := by
  let E : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorComp a φ).app M ≪≫ restrictFrame a e
  let F : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      (Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f
  refine ⟨frameChange E F, fun s => ?_⟩
  have H := coefficient_change E F (restrictSection (a ≫ φ) s)
  have hE : coefficient E (restrictSection (a ≫ φ) s) =
      a.appTop (coefficient e (restrictSection φ s)) := coefficient_restrict_comp a φ e s
  have hF : coefficient F (restrictSection (a ≫ φ) s) =
      b.appTop (coefficient f (restrictSection ψ s)) := by
    change coefficient ((Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      ((Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f)) _ = _
    rw [coefficient_transport]
    change coefficient _ (restrictSection (a ≫ φ) s ≫
      (Scheme.Modules.restrictFunctorCongr h).hom.app M) = _
    rw [restrictSection_congr]
    exact coefficient_restrict_comp b ψ f s
  rwa [hE, hF] at H

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

def scalarEnd (r : Γ(X, ⊤)) : O X ⟶ O X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma endValue_scalarEnd (r : Γ(X, ⊤)) : endValue (scalarEnd r) = r := by
  change X.presheaf.map (𝟙 _) r * 1 = r
  simp

lemma endValue_injective : Function.Injective (endValue (X := X)) := by
  intro f g h
  ext U a
  change Γ(X, U) at a
  change f.app U a = g.app U a
  rw [end_apply f U a, end_apply g U a]
  rw [end_naturality f U, end_naturality g U, h]

lemma end_isIso_iff (f : O X ⟶ O X) : IsIso f ↔ IsUnit (endValue f) := by
  constructor
  · intro h
    let := h
    refine isUnit_iff_exists_inv.mpr ⟨endValue (inv f), ?_⟩
    rw [← endValue_comp]
    simp
  · rintro ⟨u, hu⟩
    refine ⟨⟨scalarEnd ↑u⁻¹, ?_, ?_⟩⟩
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.val_inv u
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.inv_val u

lemma coefficient_isUnit_iff {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    IsUnit (coefficient e s) ↔ IsIso s := by
  change IsUnit (endValue (s ≫ e.hom)) ↔ _
  rw [← end_isIso_iff]
  exact isIso_comp_right_iff s e.hom

end
end MaximalSeshadri.Frames

end
end
end

end OAI
