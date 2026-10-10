import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.MultiplierDescent

namespace OAI

/-! Twisted Pushforward. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat

namespace NumericalDimensionOne
section
variable {n : ℕ} (Y : CanonicalModel n) (D : WeilDivisor Y.scheme)
    (Δ : QWeilDivisor Y.scheme) (W : ComplexProjectiveVariety)
    (hW : IsSmoothNfold W n) [StalkwiseNormal W.scheme]
    (π : W.scheme ⟶ Y.scheme) [IsDominant π] [IsProper π]
    (hbir : IsBirationalMorphism π) (hπ : π ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback π (rationalWeilDivisor Y.canonical + Δ) Q)
    (P : WeilDivisor W.scheme) (hP : IsCartierPullback π D P)

noncomputable def twistedToRoundupFunction (U : Y.scheme.Opens)
    (s : divisorFunctionSubmodule D U) (a : valuativeMultiplierIdeal Y Δ U) :
    (ModuleCat.restrictScalars (π.app U).hom).obj
      (ModuleCat.of Γ(W.scheme,π ⁻¹ᵁ U)
        (divisorFunctionSubmodule (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q)) (π ⁻¹ᵁ U))) :=
  ⟨fun x => dominantFunctionFieldMap π (s.1 ⟨π x.1,x.2⟩) *
      ((multiplierToRoundupApp Y Δ W hW π hbir hπ KW hKW Q hQ U).hom a).1 x,
      by
        let s' : divisorFunctionSubmodule P (π ⁻¹ᵁ U) :=
          ⟨fun x : π ⁻¹ᵁ U => dominantFunctionFieldMap π (s.1 ⟨π x.1,x.2⟩),
            divisorFunctionLocal_pullback π hP s⟩
        let t' : divisorFunctionSubmodule
            (ceilQWeilDivisor (rationalWeilDivisor KW-Q)) (π ⁻¹ᵁ U) :=
          (multiplierToRoundupApp Y Δ W hW π hbir hπ KW hKW Q hQ U).hom a
        have hh : (divisorFunctionLocal
            (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q))).pred
            (fun x : π ⁻¹ᵁ U => dominantFunctionFieldMap π (s.1 ⟨π x.1,x.2⟩) *
              ((multiplierToRoundupApp Y Δ W hW π hbir hπ KW hKW Q hQ U).hom a).1 x) :=
          divisorFunctionLocal_mul s' t'
        exact hh⟩

noncomputable def twistedToRoundupLinear (U : Y.scheme.Opens)
    (s : divisorFunctionSubmodule D U) :
    valuativeMultiplierIdeal Y Δ U →ₗ[Γ(Y.scheme,U)]
      (ModuleCat.restrictScalars (π.app U).hom).obj
      (ModuleCat.of Γ(W.scheme,π ⁻¹ᵁ U)
        (divisorFunctionSubmodule (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q)) (π ⁻¹ᵁ U))) where
  toFun := twistedToRoundupFunction Y D Δ W hW π hbir hπ KW hKW Q hQ P hP U s
  map_add' := by
    intro a b
    apply Subtype.ext
    funext x
    let y : U := ⟨π x.1,x.2⟩
    change dominantFunctionFieldMap π (s.1 y) *
        dominantFunctionFieldMap π (regularFunctionValues U (a.1+b.1) y) =
      dominantFunctionFieldMap π (s.1 y) * dominantFunctionFieldMap π (regularFunctionValues U a.1 y) +
        dominantFunctionFieldMap π (s.1 y) * dominantFunctionFieldMap π (regularFunctionValues U b.1 y)
    simp only [map_add,Pi.add_apply,mul_add]
  map_smul' := by
    intro a b
    apply Subtype.ext
    funext x
    let y : U := ⟨π x.1,x.2⟩
    change dominantFunctionFieldMap π (s.1 y) *
        dominantFunctionFieldMap π (regularFunctionValues U (a*b.1) y) =
      regularFunctionValues (π ⁻¹ᵁ U) (π.app U a) x *
        (dominantFunctionFieldMap π (s.1 y) * dominantFunctionFieldMap π (regularFunctionValues U b.1 y))
    have ha := regularFunctionValues_pullback π U a x
    change regularFunctionValues (π ⁻¹ᵁ U) (π.app U a) x =
      dominantFunctionFieldMap π (regularFunctionValues U a y) at ha
    rw [ha]
    simp only [map_mul,Pi.mul_apply]
    ring

noncomputable def twistedToRoundupBilinear (U : Y.scheme.Opens) :
    divisorFunctionSubmodule D U →ₗ[Γ(Y.scheme,U)]
      valuativeMultiplierIdeal Y Δ U →ₗ[Γ(Y.scheme,U)]
        (ModuleCat.restrictScalars (π.app U).hom).obj
      (ModuleCat.of Γ(W.scheme,π ⁻¹ᵁ U)
        (divisorFunctionSubmodule (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q)) (π ⁻¹ᵁ U))) where
  toFun := twistedToRoundupLinear Y D Δ W hW π hbir hπ KW hKW Q hQ P hP U
  map_add' := by
    intro s t
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext x
    change dominantFunctionFieldMap π (s.1 ⟨π x.1,x.2⟩+t.1 ⟨π x.1,x.2⟩) * _ = _
    rw [map_add,add_mul]
    rfl
  map_smul' := by
    intro a s
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    funext x
    change dominantFunctionFieldMap π
      (regularFunctionValues U a ⟨π x.1,x.2⟩ * s.1 ⟨π x.1,x.2⟩) * _ =
      regularFunctionValues (π ⁻¹ᵁ U) (π.app U a) x * (_ * _)
    rw [regularFunctionValues_pullback,map_mul,mul_assoc]

noncomputable def twistedToRoundupApp (U : Y.scheme.Opens) :
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (divisorModulePresheaf D)
      (multiplierModulePresheaf Y Δ)).obj (op U) ⟶
        ((SheafOfModules.pushforward π.toRingCatSheafHom).obj
          (divisorModuleSheaf (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q)))).val.obj (op U) :=
  ModuleCat.ofHom (R := Γ(Y.scheme,U))
    (X := ModuleCat.of Γ(Y.scheme,U) (TensorProduct Γ(Y.scheme,U)
      (divisorFunctionSubmodule D U) (valuativeMultiplierIdeal Y Δ U)))
    (Y := (ModuleCat.restrictScalars (π.app U).hom).obj
      (ModuleCat.of Γ(W.scheme,π ⁻¹ᵁ U)
        (divisorFunctionSubmodule (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q)) (π ⁻¹ᵁ U))))
    (TensorProduct.lift
      (twistedToRoundupBilinear Y D Δ W hW π hbir hπ KW hKW Q hQ P hP U))

noncomputable def twistedToRoundupPresheaf :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (divisorModulePresheaf D)
      (multiplierModulePresheaf Y Δ) ⟶
        ((SheafOfModules.pushforward π.toRingCatSheafHom).obj
          (divisorModuleSheaf (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q)))).val where
  app := fun U => twistedToRoundupApp Y D Δ W hW π hbir hπ KW hKW Q hQ P hP U.unop
  naturality := by
    intro U V i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s a
    change divisorFunctionSubmodule D U.unop at s
    change valuativeMultiplierIdeal Y Δ U.unop at a
    apply Subtype.ext
    funext x
    change dominantFunctionFieldMap π (s.1 _) * dominantFunctionFieldMap π
        (regularFunctionValues V.unop (Y.scheme.presheaf.map i a.1) ⟨π x.1,x.2⟩) =
      dominantFunctionFieldMap π (s.1 _) * dominantFunctionFieldMap π
        (regularFunctionValues U.unop a.1 ⟨π x.1,_⟩)
    exact congrArg (fun z => dominantFunctionFieldMap π (s.1 (i.unop ⟨π x.1,x.2⟩)) *
      dominantFunctionFieldMap π z) (regularFunctionValues_res i.unop a.1 ⟨π x.1,x.2⟩)
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat

namespace NumericalDimensionOne
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y]

omit [StalkwiseNormal X] in
lemma divisorSectionOn_div_equation [StalkwiseNormal X] {P R : WeilDivisor X} {U : X.Opens}
    {g : X.functionField} (hg : g ≠ 0)
    (hP : ∀ p : PrimeDivisor X, p.1 ∈ U → P p = X.ord g p.1)
    (r : X.functionField) :
    IsDivisorSectionOn R U r ↔ IsDivisorSectionOn (P+R) U (r/g) := by
  by_cases hr : r = 0
  · simp [IsDivisorSectionOn,hr]
  simp only [IsDivisorSectionOn,hr,div_ne_zero hr hg,false_or]
  constructor <;> intro h p hp
  · rw [order_div hr hg,Finsupp.add_apply,hP p hp]
    have := h p hp
    omega
  · have hh := h p hp
    rw [order_div hr hg,Finsupp.add_apply,hP p hp] at hh
    omega

lemma divisorFunctionLocal_div_equation {P R : WeilDivisor X} {U : X.Opens}
    {g : X.functionField} (hg : g ≠ 0)
    (hP : ∀ p : PrimeDivisor X, p.1 ∈ U → P p = X.ord g p.1)
    (s : divisorFunctionSubmodule R U) :
    (divisorFunctionLocal (P+R)).pred (fun x => s.1 x/g) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    obtain ⟨r,hr,hs⟩ := (divisorFunctionLocal_iff s.1).mp s.2
    apply PrelocalPredicate.sheafifyOf
    refine ⟨r/g,?_,(divisorSectionOn_div_equation hg hP r).mp hs⟩
    intro x
    dsimp only
    rw [hr]
  · have he : (fun x => s.1 x/g) = 0 := by
      funext x
      exact (hU ⟨x⟩).elim
    rw [he]
    exact divisorFunctionLocal_zero _ _

lemma divisorFunctionLocal_mul_equation {P R : WeilDivisor X} {U : X.Opens}
    {g : X.functionField} (hg : g ≠ 0)
    (hP : ∀ p : PrimeDivisor X, p.1 ∈ U → P p = X.ord g p.1)
    (s : divisorFunctionSubmodule (P+R) U) :
    (divisorFunctionLocal R).pred (fun x => s.1 x*g) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    obtain ⟨r,hr,hs⟩ := (divisorFunctionLocal_iff s.1).mp s.2
    apply PrelocalPredicate.sheafifyOf
    refine ⟨r*g,?_,(divisorSectionOn_div_equation hg hP (r*g)).mpr ?_⟩
    · intro x
      dsimp only
      rw [hr]
    · simpa only [mul_div_cancel_right₀ r hg] using hs
  · have he : (fun x => s.1 x*g) = 0 := by
      funext x
      exact (hU ⟨x⟩).elim
    rw [he]
    exact divisorFunctionLocal_zero _ _

noncomputable def divisorPushforwardShiftEquiv (f : X ⟶ Y)
    (U : Y.Opens) (P R : WeilDivisor X) (g : X.functionField) (hg : g ≠ 0)
    (hP : ∀ p : PrimeDivisor X, f p.1 ∈ U → P p = X.ord g p.1) :
    (ModuleCat.restrictScalars (f.app U).hom).obj
      (ModuleCat.of Γ(X,f ⁻¹ᵁ U) (divisorFunctionSubmodule R (f ⁻¹ᵁ U))) ≃ₗ[Γ(Y,U)]
        (ModuleCat.restrictScalars (f.app U).hom).obj
          (ModuleCat.of Γ(X,f ⁻¹ᵁ U) (divisorFunctionSubmodule (P+R) (f ⁻¹ᵁ U))) where
  toFun s := ⟨fun x => s.1 x/g,divisorFunctionLocal_div_equation hg hP s⟩
  invFun s := ⟨fun x => s.1 x*g,divisorFunctionLocal_mul_equation hg hP s⟩
  left_inv := by
    intro s
    apply Subtype.ext
    funext x
    exact div_mul_cancel₀ _ hg
  right_inv := by
    intro s
    apply Subtype.ext
    funext x
    exact mul_div_cancel_right₀ _ hg
  map_add' := by
    intro s t
    apply Subtype.ext
    funext x
    exact add_div _ _ _
  map_smul' := by
    intro a s
    apply Subtype.ext
    funext x
    exact mul_div_assoc _ _ _
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat

namespace NumericalDimensionOne
section
variable {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (D : WeilDivisor Y.scheme) (Δ : QWeilDivisor Y.scheme) (hΔ : 0 ≤ Δ)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    [StalkwiseNormal W.scheme]
    (π : W.scheme ⟶ Y.scheme) [IsDominant π] [IsProper π]
    (hbir : IsBirationalMorphism π) (hπ : π ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback π (rationalWeilDivisor Y.canonical + Δ) Q)
    (P : WeilDivisor W.scheme) (hP : IsCartierPullback π D P)
    {ι : Type*} [Fintype ι] (E : ι → WeilDivisor W.scheme)
    (hE : IsSimpleNormalCrossingsDivisorFamily W n E) (c : ι → ℚ)
    (hSNC : Q - rationalWeilDivisor KW = ∑ i, c i • rationalWeilDivisor (E i))

include hY hΔ hE hSNC in
lemma twistedToRoundupApp_bijective_on_chart (U : Y.scheme.Opens) [Nonempty U]
    (g : Y.scheme.functionField) (hg : g ≠ 0)
    (hDg : ∀ p : PrimeDivisor Y.scheme, p.1 ∈ U → D p = Y.scheme.ord g p.1) :
    Function.Bijective (twistedToRoundupApp Y D Δ W hW π hbir hπ KW hKW Q hQ P hP U).hom := by
  let eD := cartierOpenChartEquiv hg hDg
  let eJ : valuativeMultiplierIdeal Y Δ U ≃ₗ[Γ(Y.scheme,U)]
      (ModuleCat.restrictScalars (π.app U).hom).obj
        (ModuleCat.of Γ(W.scheme,π ⁻¹ᵁ U)
          (divisorFunctionSubmodule (ceilQWeilDivisor (rationalWeilDivisor KW-Q)) (π ⁻¹ᵁ U))) :=
    LinearEquiv.ofBijective
    (multiplierToRoundupApp Y Δ W hW π hbir hπ KW hKW Q hQ U).hom
    (multiplierToRoundupApp_bijective Y hY Δ hΔ W hW π hbir hπ KW hKW Q hQ E hE c hSNC U)
  let eP := divisorPushforwardShiftEquiv π U P
    (ceilQWeilDivisor (rationalWeilDivisor KW-Q)) (dominantFunctionFieldMap π g)
    ((map_ne_zero _).mpr hg) (hP.eq_ord_on_open hg hDg)
  let e := (((TensorProduct.congr eD.symm
    (LinearEquiv.refl Γ(Y.scheme,U) (valuativeMultiplierIdeal Y Δ U))).trans
      (TensorProduct.lid Γ(Y.scheme,U) (valuativeMultiplierIdeal Y Δ U))).trans eJ).trans eP
  let L : TensorProduct Γ(Y.scheme,U) (divisorFunctionSubmodule D U)
      (valuativeMultiplierIdeal Y Δ U) →ₗ[Γ(Y.scheme,U)]
        (ModuleCat.restrictScalars (π.app U).hom).obj
          (ModuleCat.of Γ(W.scheme,π ⁻¹ᵁ U)
            (divisorFunctionSubmodule (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q)) (π ⁻¹ᵁ U))) :=
    (twistedToRoundupApp Y D Δ W hW π hbir hπ KW hKW Q hQ P hP U).hom
  change Function.Bijective L
  have he : L = e.toLinearMap := by
    apply TensorProduct.ext'
    intro s a
    obtain ⟨b,rfl⟩ := eD.surjective s
    apply Subtype.ext
    funext x
    simp only [e,LinearEquiv.trans_apply,LinearEquiv.coe_toLinearMap,
      TensorProduct.congr_tmul,LinearEquiv.symm_apply_apply,TensorProduct.lid_tmul]
    change dominantFunctionFieldMap π (Y.scheme.germToFunctionField U b/g) *
        dominantFunctionFieldMap π (regularFunctionValues U a.1 ⟨π x.1,x.2⟩) =
      dominantFunctionFieldMap π (regularFunctionValues U (b*a.1) ⟨π x.1,x.2⟩) /
        dominantFunctionFieldMap π g
    rw [map_div₀,regularFunctionValues_eq,regularFunctionValues_eq,map_mul,map_mul]
    ring
  exact (congrArg (fun t => Function.Bijective t) (congrArg DFunLike.coe he)).mpr e.bijective
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
universe u
variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u})
    {M N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
noncomputable def moduleStalkMap (f : M ⟶ N) (x : X) :
    TopCat.Presheaf.stalk M.presheaf x ⟶ TopCat.Presheaf.stalk N.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf _).map f)
lemma moduleStalkMap_germ (f : M ⟶ N) (x : X) (U : Opens X)
    (hx : x ∈ U) (s : M.obj (op U)) :
    moduleStalkMap R f x (TopCat.Presheaf.germ M.presheaf U x hx s) =
      TopCat.Presheaf.germ N.presheaf U x hx (f.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
lemma moduleStalkMap_smul_germ (f : M ⟶ N) (x : X) (U : Opens X)
    (hx : x ∈ U) (a : R.obj (op U)) (s : M.obj (op U)) :
    moduleStalkMap R f x (R.germ U x hx a • TopCat.Presheaf.germ M.presheaf U x hx s) =
      R.germ U x hx a • moduleStalkMap R f x (TopCat.Presheaf.germ M.presheaf U x hx s) := by
  rw [← M.germ_smul x U hx a s,moduleStalkMap_germ,moduleStalkMap_germ]
  rw [map_smul]
  exact N.germ_smul x U hx a (f.app (op U) s)
noncomputable def moduleStalkLinearMap (f : M ⟶ N) (x : X) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) →ₗ[R.stalk x]
      ↑(TopCat.Presheaf.stalk N.presheaf x) where
  toFun := moduleStalkMap R f x
  map_add' := map_add _
  map_smul' := by
    intro a b
    obtain ⟨U,hxU,a,rfl⟩ := R.exists_germ_eq a
    obtain ⟨V,hxV,b,rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf b
    let i : U ⊓ V ⟶ U := homOfLE inf_le_left
    let j : U ⊓ V ⟶ V := homOfLE inf_le_right
    have hr := R.germ_res_apply i x ⟨hxU,hxV⟩ a
    have hs := TopCat.Presheaf.germ_res_apply M.presheaf j x ⟨hxU,hxV⟩ b
    rw [← hr,← hs]
    exact moduleStalkMap_smul_germ R f x (U ⊓ V) ⟨hxU,hxV⟩ _ _
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
universe u
variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u})
    {M N : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
theorem moduleStalkMap_bijective_of_local (f : M ⟶ N) {U : Opens X}
    (h : ∀ V ≤ U, Function.Bijective (f.app (op V))) {x : X} (hx : x ∈ U) :
    Function.Bijective (moduleStalkMap R f x) := by
  constructor
  · intro a b hab
    obtain ⟨V,hVU,hxV,a,rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf a hx
    obtain ⟨W,hWU,hxW,b,rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf b hx
    rw [moduleStalkMap_germ R f x V hxV a,moduleStalkMap_germ R f x W hxW b] at hab
    obtain ⟨T,hxT,i,j,hij⟩ := TopCat.Presheaf.germ_eq N.presheaf x hxV hxW _ _ hab
    apply TopCat.Presheaf.germ_ext M.presheaf T hxT i j
    apply (h T (le_trans (leOfHom i) hVU)).1
    exact (PresheafOfModules.naturality_apply f i.op a).trans
      (hij.trans (PresheafOfModules.naturality_apply f j.op b).symm)
  · intro a
    obtain ⟨V,hVU,hxV,a,rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf a hx
    obtain ⟨b,hb⟩ := (h V hVU).2 a
    refine ⟨TopCat.Presheaf.germ M.presheaf V x hxV b,?_⟩
    rw [moduleStalkMap_germ,hb]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
section
variable {n : ℕ} (Y : CanonicalModel n) (D : WeilDivisor Y.scheme)
    (Δ : QWeilDivisor Y.scheme) (W : ComplexProjectiveVariety)
    (hW : IsSmoothNfold W n) [StalkwiseNormal W.scheme]
    (π : W.scheme ⟶ Y.scheme) [IsDominant π] [IsProper π]
    (hbir : IsBirationalMorphism π) (hπ : π ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback π (rationalWeilDivisor Y.canonical + Δ) Q)
    (P : WeilDivisor W.scheme) (hP : IsCartierPullback π D P)

noncomputable def twistedToRoundup : twistedMultiplierModuleSheaf Y D Δ ⟶
    (SheafOfModules.pushforward π.toRingCatSheafHom).obj
      (divisorModuleSheaf (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q))) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 Y.scheme.ringCatSheaf.obj)).symm
    (twistedToRoundupPresheaf Y D Δ W hW π hbir hπ KW hKW Q hQ P hP)

lemma twistedToRoundup_fac :
    (PresheafOfModules.toPresheaf Y.scheme.ringCatSheaf.obj).map
      (twistedToRoundupPresheaf Y D Δ W hW π hbir hπ KW hKW Q hQ P hP) =
    CategoryTheory.toSheafify (Opens.grothendieckTopology Y.scheme)
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (divisorModulePresheaf D)
        (multiplierModulePresheaf Y Δ)).presheaf ≫
      (PresheafOfModules.toPresheaf Y.scheme.ringCatSheaf.obj).map
        (twistedToRoundup Y D Δ W hW π hbir hπ KW hKW Q hQ P hP).val := by
  have hh := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 Y.scheme.ringCatSheaf.obj) (twistedToRoundup Y D Δ W hW π hbir hπ KW hKW Q hQ P hP)
  have he := (PresheafOfModules.sheafificationHomEquiv (𝟙 Y.scheme.ringCatSheaf.obj)
    (P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (divisorModulePresheaf D)
      (multiplierModulePresheaf Y Δ))
    (F := (SheafOfModules.pushforward π.toRingCatSheafHom).obj
      (divisorModuleSheaf (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q))))).apply_symm_apply
        (twistedToRoundupPresheaf Y D Δ W hW π hbir hπ KW hKW Q hQ P hP)
  exact (congrArg ((PresheafOfModules.toPresheaf Y.scheme.ringCatSheaf.obj).map) he).symm.trans hh
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne
section
variable {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (D : WeilDivisor Y.scheme) (hD : IsCartierDivisor D)
    (Δ : QWeilDivisor Y.scheme) (hΔ : 0 ≤ Δ)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    [StalkwiseNormal W.scheme]
    (π : W.scheme ⟶ Y.scheme) [IsDominant π] [IsProper π]
    (hbir : IsBirationalMorphism π) (hπ : π ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback π (rationalWeilDivisor Y.canonical + Δ) Q)
    (P : WeilDivisor W.scheme) (hP : IsCartierPullback π D P)
    {ι : Type*} [Fintype ι] (E : ι → WeilDivisor W.scheme)
    (hE : IsSimpleNormalCrossingsDivisorFamily W n E) (c : ι → ℚ)
    (hSNC : Q - rationalWeilDivisor KW = ∑ i, c i • rationalWeilDivisor (E i))

include hY hD hΔ hE hSNC in
lemma twistedToRoundupPresheaf_stalk_bijective (x : Y.scheme) :
    Function.Bijective (moduleStalkMap Y.scheme.presheaf
      (twistedToRoundupPresheaf Y D Δ W hW π hbir hπ KW hKW Q hQ P hP) x) := by
  classical
  obtain ⟨U,_,hxU,g,hg,hDg⟩ := hD x
  apply moduleStalkMap_bijective_of_local Y.scheme.presheaf _ (x := x) (U := U) _ hxU
  intro V hVU
  by_cases hV : Nonempty V
  · let := hV
    exact twistedToRoundupApp_bijective_on_chart Y hY D Δ hΔ W hW π hbir hπ KW hKW Q hQ
      P hP E hE c hSNC V g hg (fun p hp => hDg p (hVU hp))
  · let : IsEmpty V := ⟨fun z => hV ⟨z⟩⟩
    let : Subsingleton (divisorFunctionSubmodule D V) := ⟨fun a b =>
      Subtype.ext (funext fun z => (hV ⟨z⟩).elim)⟩
    constructor
    · intro a b _
      change TensorProduct Γ(Y.scheme,V) (divisorFunctionSubmodule D V)
        (valuativeMultiplierIdeal Y Δ V) at a b
      exact Subsingleton.elim a b
    · intro a
      refine ⟨0,?_⟩
      apply Subtype.ext
      funext z
      exact (hV ⟨⟨π z.1,z.2⟩⟩).elim

include hY hD hΔ hE hSNC in
lemma twistedToRoundup_stalk_bijective (x : Y.scheme) :
    Function.Bijective (moduleStalkMap Y.scheme.presheaf
      (twistedToRoundup Y D Δ W hW π hbir hπ KW hKW Q hQ P hP).val x) := by
  let F := (PresheafOfModulesOfCommRing.Monoidal.tensorObj (divisorModulePresheaf D)
    (multiplierModulePresheaf Y Δ)).presheaf
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology Y.scheme) F
  let G := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  have : IsIso (G.map η) := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ F
  have hη : Function.Bijective (G.map η) := (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hf := twistedToRoundupPresheaf_stalk_bijective Y hY D hD Δ hΔ W hW π hbir hπ KW hKW Q hQ
    P hP E hE c hSNC x
  have heq : moduleStalkMap Y.scheme.presheaf
      (twistedToRoundupPresheaf Y D Δ W hW π hbir hπ KW hKW Q hQ P hP) x =
    G.map η ≫ moduleStalkMap Y.scheme.presheaf
      (twistedToRoundup Y D Δ W hW π hbir hπ KW hKW Q hQ P hP).val x := by
    exact (congrArg (fun f => G.map f)
      (twistedToRoundup_fac Y D Δ W hW π hbir hπ KW hKW Q hQ P hP)).trans (G.map_comp _ _)
  rw [heq] at hf
  change Function.Bijective ((moduleStalkMap Y.scheme.presheaf
    (twistedToRoundup Y D Δ W hW π hbir hπ KW hKW Q hQ P hP).val x) ∘ (G.map η)) at hf
  constructor
  · intro a b hab
    obtain ⟨c,rfl⟩ := hη.2 a
    obtain ⟨d,rfl⟩ := hη.2 b
    exact congrArg (G.map η) (hf.1 hab)
  · intro a
    obtain ⟨b,hb⟩ := hf.2 a
    exact ⟨G.map η b,hb⟩
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open CategoryTheory TopologicalSpace Opposite

namespace NumericalDimensionOne

theorem twistedMultiplierModuleSheaf_iso_pushforward_on_snc_model
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (D : WeilDivisor Y.scheme) (hD : IsCartierDivisor D)
    (Δ : QWeilDivisor Y.scheme) (hΔ : 0 ≤ Δ)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    [StalkwiseNormal W.scheme]
    (π : W.scheme ⟶ Y.scheme) [IsDominant π] [IsProper π]
    (hbir : IsBirationalMorphism π) (hπ : π ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback π (rationalWeilDivisor Y.canonical + Δ) Q)
    (P : WeilDivisor W.scheme) (hP : IsCartierPullback π D P)
    {ι : Type*} [Fintype ι] (E : ι → WeilDivisor W.scheme)
    (hE : IsSimpleNormalCrossingsDivisorFamily W n E) (c : ι → ℚ)
    (hSNC : Q - rationalWeilDivisor KW = ∑ i, c i • rationalWeilDivisor (E i)) :
    Nonempty (twistedMultiplierModuleSheaf Y D Δ ≅
      (SheafOfModules.pushforward π.toRingCatSheafHom).obj
        (divisorModuleSheaf (P + ceilQWeilDivisor (rationalWeilDivisor KW - Q)))) := by
  let f := twistedToRoundup Y D Δ W hW π hbir hπ KW hKW Q hQ P hP
  have hf : IsIso f := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    let f' : (SheafOfModules.toSheaf Y.scheme.ringCatSheaf).obj
        (twistedMultiplierModuleSheaf Y D Δ) ⟶
      (SheafOfModules.toSheaf Y.scheme.ringCatSheaf).obj
        ((SheafOfModules.pushforward π.toRingCatSheafHom).obj
          (divisorModuleSheaf (P+ceilQWeilDivisor (rationalWeilDivisor KW-Q)))) :=
      (SheafOfModules.toSheaf Y.scheme.ringCatSheaf).map f
    exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f' U
      (fun x _ => twistedToRoundup_stalk_bijective Y hY D hD Δ hΔ W hW π hbir hπ KW hKW Q hQ
        P hP E hE c hSNC x)
  let := hf
  exact ⟨asIso f⟩
end NumericalDimensionOne

end OAI
