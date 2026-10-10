import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.NormalDivisors

namespace OAI

/-! Rational Pullbacks. -/

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne
section CartierLocalUnits
variable {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y] [StalkwiseNormal Y]

omit [StalkwiseNormal Y] in
lemma order_div {g h : Y.functionField} (hg : g ≠ 0) (hh : h ≠ 0) (y : Y) :
    Y.ord (g / h) y = Y.ord g y - Y.ord h y := by
  rw [div_eq_mul_inv, Y.ord_mul hg (inv_ne_zero hh), order_inv h hh, sub_eq_add_neg]

lemma affine_unit_of_zero_orders {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U]
    {g : Y.functionField} (hg : g ≠ 0)
    (hord : ∀ p : PrimeDivisor Y, p.1 ∈ U → Y.ord g p.1 = 0) :
    ∃ u : Γ(Y, U), IsUnit u ∧ Y.germToFunctionField U u = g := by
  obtain ⟨u, hu⟩ := (affine_regular_iff_nonnegative_orders hU g).mpr
    (Or.inr (fun p hp => le_of_eq (hord p hp).symm))
  obtain ⟨v, hv⟩ := (affine_regular_iff_nonnegative_orders hU g⁻¹).mpr
    (Or.inr (fun p hp => by rw [order_inv g hg, hord p hp]; omega))
  refine ⟨u, ?_, hu⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨v, ?_⟩
  apply Y.germToFunctionField_injective U
  rw [map_mul, hu, hv, mul_inv_cancel₀ hg, map_one]

lemma local_equation_ratio_unit {D : WeilDivisor Y} {U V : Y.Opens}
    {g h : Y.functionField} (hg : g ≠ 0) (hh : h ≠ 0)
    (hDg : ∀ p : PrimeDivisor Y, p.1 ∈ U → D p = Y.ord g p.1)
    (hDh : ∀ p : PrimeDivisor Y, p.1 ∈ V → D p = Y.ord h p.1)
    {y : Y} (hyU : y ∈ U) (hyV : y ∈ V) :
    ∃ u : Y.presheaf.stalk y, IsUnit u ∧
      algebraMap (Y.presheaf.stalk y) Y.functionField u = g / h := by
  obtain ⟨W, hW, hyW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ U ⊓ V from ⟨hyU, hyV⟩)
  let : Nonempty W := ⟨⟨y, hyW⟩⟩
  obtain ⟨u, hu, heq⟩ := affine_unit_of_zero_orders hW (div_ne_zero hg hh)
    (fun p hp => by rw [order_div hg hh, ← hDg p (hsub hp).1, ← hDh p (hsub hp).2]; omega)
  refine ⟨Y.presheaf.germ W y hyW u, hu.map (Y.presheaf.germ W y hyW).hom, ?_⟩
  rw [Y.algebraMap_germ_eq_germToFunctionField hyW, heq]

end CartierLocalUnits

section CartierLocalPullback
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal Y]

omit [IsIntegral Y] [IsLocallyNoetherian Y] [StalkwiseNormal Y] in
lemma order_stalk_unit (p : PrimeDivisor X) {a : X.presheaf.stalk p.1}
    (ha : IsUnit a) : X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField a) p.1 = 0 := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk p.1) := krullDimLE_of_coheight_le p.2.le
  apply (X.ord_eq_iff p.2 (ha.map (algebraMap _ _)).ne_zero).mpr
  exact Ring.ordFrac_of_isUnit ha

lemma pulled_equation_order_eq (f : X ⟶ Y) [IsDominant f]
    {D : WeilDivisor Y} {U V : Y.Opens} {g h : Y.functionField}
    (hg : g ≠ 0) (hh : h ≠ 0)
    (hDg : ∀ p : PrimeDivisor Y, p.1 ∈ U → D p = Y.ord g p.1)
    (hDh : ∀ p : PrimeDivisor Y, p.1 ∈ V → D p = Y.ord h p.1)
    (p : PrimeDivisor X) (hpU : f p.1 ∈ U) (hpV : f p.1 ∈ V) :
    X.ord (dominantFunctionFieldMap f g) p.1 = X.ord (dominantFunctionFieldMap f h) p.1 := by
  obtain ⟨u, hu, heq⟩ := local_equation_ratio_unit hg hh hDg hDh hpU hpV
  have ho := order_stalk_unit p (hu.map (f.stalkMap p.1).hom)
  rw [← dominantFunctionFieldMap_algebraMap f p.1 u, heq, map_div₀,
    order_div ((map_ne_zero (dominantFunctionFieldMap f)).mpr hg)
      ((map_ne_zero (dominantFunctionFieldMap f)).mpr hh)] at ho
  omega

end CartierLocalPullback
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne

theorem exists_cartierPullback {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal Y] [CompactSpace X]
    (f : X ⟶ Y) [IsDominant f] (D : WeilDivisor Y) (hD : IsCartierDivisor D) :
    ∃ E : WeilDivisor X, IsCartierPullback f D E := by
  classical
  choose U hU hxU g hg hDg using hD
  let c : PrimeDivisor X → ℤ := fun p => X.ord (dominantFunctionFieldMap f (g (f p.1))) p.1
  have hc (p : PrimeDivisor X) (y : Y) (hp : f p.1 ∈ U y) :
      c p = X.ord (dominantFunctionFieldMap f (g y)) p.1 :=
    pulled_equation_order_eq f (hg (f p.1)) (hg y) (hDg (f p.1)) (hDg y)
      p (hxU (f p.1)) hp
  let y₀ : Y := f (genericPoint X)
  let V : X.Opens := f ⁻¹ᵁ U y₀
  have hV : (V : Set X)ᶜ ≠ Set.univ := by
    intro h
    have hm : genericPoint X ∈ (V : Set X)ᶜ := by rw [h]; trivial
    exact hm (hxU y₀)
  have hfinite : (Function.support c).Finite := by
    apply ((ord_finite_support (dominantFunctionFieldMap f (g y₀))).union
      (finite_primeDivisors_in_closed V.isOpen.isClosed_compl hV)).subset
    intro p hp
    by_cases hpV : f p.1 ∈ U y₀
    · left
      change X.ord (dominantFunctionFieldMap f (g y₀)) p.1 ≠ 0
      intro hz
      exact hp ((hc p y₀ hpV).trans hz)
    · exact Or.inr hpV
  let E : WeilDivisor X := Finsupp.ofSupportFinite c hfinite
  refine ⟨E, ?_⟩
  intro x
  refine ⟨U (f x), hU (f x), hxU (f x), g (f x), hg (f x), hDg (f x), ?_⟩
  intro p hp
  exact hc p (f x) hp

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne
section PullbackProperties
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

theorem IsCartierPullback.isCartier {f : X ⟶ Y} [IsDominant f]
    {D : WeilDivisor Y} {E : WeilDivisor X} (hE : IsCartierPullback f D E) :
    IsCartierDivisor E := by
  intro x
  obtain ⟨U, _, hx, g, hg, _, hEg⟩ := hE x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ U from hx)
  refine ⟨V, hV, hxV, dominantFunctionFieldMap f g,
    (map_ne_zero _).mpr hg, ?_⟩
  exact fun p hp => hEg p (hVU hp)

theorem IsCartierPullback.unique [StalkwiseNormal Y] {f : X ⟶ Y} [IsDominant f]
    {D : WeilDivisor Y} {E F : WeilDivisor X}
    (hE : IsCartierPullback f D E) (hF : IsCartierPullback f D F) : E = F := by
  ext p
  obtain ⟨U, _, hpU, g, hg, hDg, hEg⟩ := hE p.1
  obtain ⟨V, _, hpV, h, hh, hDh, hFh⟩ := hF p.1
  rw [hEg p hpU, hFh p hpV]
  exact pulled_equation_order_eq f hg hh hDg hDh p hpU hpV

theorem IsCartierPullback.add {f : X ⟶ Y} [IsDominant f]
    {D₁ D₂ : WeilDivisor Y} {E₁ E₂ : WeilDivisor X}
    (h₁ : IsCartierPullback f D₁ E₁) (h₂ : IsCartierPullback f D₂ E₂) :
    IsCartierPullback f (D₁ + D₂) (E₁ + E₂) := by
  intro x
  obtain ⟨U, _, hxU, g, hg, hDg, hEg⟩ := h₁ x
  obtain ⟨V, _, hxV, h, hh, hDh, hEh⟩ := h₂ x
  obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  refine ⟨W, hW, hxW, g * h, mul_ne_zero hg hh, ?_, ?_⟩
  · intro p hp
    simp only [Finsupp.add_apply, hDg p (hsub hp).1, hDh p (hsub hp).2,
      Y.ord_mul hg hh]
  · intro p hp
    simp only [Finsupp.add_apply, hEg p (hsub hp).1, hEh p (hsub hp).2,
      map_mul, X.ord_mul ((map_ne_zero _).mpr hg) ((map_ne_zero _).mpr hh)]

theorem IsCartierPullback.neg {f : X ⟶ Y} [IsDominant f]
    {D : WeilDivisor Y} {E : WeilDivisor X} (hE : IsCartierPullback f D E) :
    IsCartierPullback f (-D) (-E) := by
  intro x
  obtain ⟨U, hU, hx, g, hg, hDg, hEg⟩ := hE x
  refine ⟨U, hU, hx, g⁻¹, inv_ne_zero hg, ?_, ?_⟩
  · intro p hp
    simp only [Finsupp.neg_apply, hDg p hp, order_inv g hg]
  · intro p hp
    simp only [Finsupp.neg_apply, hEg p hp, map_inv₀,
      order_inv (dominantFunctionFieldMap f g) ((map_ne_zero (dominantFunctionFieldMap f)).mpr hg)]

theorem isCartierPullback_zero (f : X ⟶ Y) [IsDominant f] :
    IsCartierPullback f 0 0 := by
  intro x
  let U : Y.Opens := (Y.affineCover.f (Y.affineCover.idx (f x))).opensRange
  refine ⟨U, isAffineOpen_opensRange _, Y.affineCover.covers _, 1, one_ne_zero, ?_, ?_⟩
  · intro p _; simp [order_one]
  · intro p _; simp [order_one]

theorem isCartierPullback_principal [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) [IsDominant f] (g : Y.functionField) (hg : g ≠ 0) :
    IsCartierPullback f (principalWeilDivisor g)
      (principalWeilDivisor (dominantFunctionFieldMap f g)) := by
  intro x
  let U : Y.Opens := (Y.affineCover.f (Y.affineCover.idx (f x))).opensRange
  exact ⟨U, isAffineOpen_opensRange _, Y.affineCover.covers _, g, hg,
    fun _ _ => rfl, fun _ _ => rfl⟩

end PullbackProperties
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne
section CurvePullbackDefinition
variable {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
    [IsLocallyNoetherian C] [IsLocallyNoetherian Y]

def IsPulledCartierRepresentative (f : C ⟶ Y)
    (D : WeilDivisor Y) (E : WeilDivisor C) : Prop :=
  ∃ U : Y.Opens, IsAffineOpen U ∧ f (genericPoint C) ∈ U ∧
    ∃ g : Y.functionField, g ≠ 0 ∧
      (∀ p : PrimeDivisor Y, p.1 ∈ U → D p = Y.ord g p.1) ∧
      ∀ x : C, ∃ V : Y.Opens, IsAffineOpen V ∧ f x ∈ V ∧
        ∃ h : Y.functionField, h ≠ 0 ∧
          (∀ p : PrimeDivisor Y, p.1 ∈ V → D p = Y.ord h p.1) ∧
          ∃ a : Y.presheaf.stalk (f (genericPoint C)), IsUnit a ∧
            algebraMap (Y.presheaf.stalk (f (genericPoint C))) Y.functionField a = h / g ∧
            (∀ p : PrimeDivisor C, f p.1 ∈ V →
              E p = C.ord (f.stalkMap (genericPoint C) a) p.1)

end CurvePullbackDefinition
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne
section CurvePullbackLocal
variable {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
    [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [StalkwiseNormal Y]

omit [IsIntegral Y] [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [StalkwiseNormal Y] in
lemma image_generic_mem (f : C ⟶ Y) {U : Y.Opens} {x : C} (hx : f x ∈ U) :
    f (genericPoint C) ∈ U := by
  exact (f.base.hom.map_specializes ((genericPoint_spec C).specializes trivial)).mem_open U.isOpen hx

omit [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [StalkwiseNormal Y] in
lemma algebraMap_stalkSpecializes {x y : Y} (h : x ⤳ y) (a : Y.presheaf.stalk y) :
    algebraMap (Y.presheaf.stalk x) Y.functionField (Y.presheaf.stalkSpecializes h a) =
      algebraMap (Y.presheaf.stalk y) Y.functionField a := by
  exact Y.presheaf.stalkSpecializes_comp_apply
    ((genericPoint_spec Y).specializes trivial) h a

lemma curve_equation_order_eq (f : C ⟶ Y) {D : WeilDivisor Y}
    {U V : Y.Opens} {g h anchor : Y.functionField}
    (hg : g ≠ 0) (hh : h ≠ 0) (ha : anchor ≠ 0)
    (hDg : ∀ p : PrimeDivisor Y, p.1 ∈ U → D p = Y.ord g p.1)
    (hDh : ∀ p : PrimeDivisor Y, p.1 ∈ V → D p = Y.ord h p.1)
    (a b : Y.presheaf.stalk (f (genericPoint C))) (hb : IsUnit b)
    (hag : algebraMap _ Y.functionField a = g / anchor)
    (hbh : algebraMap _ Y.functionField b = h / anchor)
    (p : PrimeDivisor C) (hpU : f p.1 ∈ U) (hpV : f p.1 ∈ V) :
    C.ord (f.stalkMap (genericPoint C) a) p.1 =
      C.ord (f.stalkMap (genericPoint C) b) p.1 := by
  obtain ⟨u, hu, heq⟩ := local_equation_ratio_unit hg hh hDg hDh hpU hpV
  let hs : genericPoint C ⤳ p.1 := (genericPoint_spec C).specializes trivial
  let uy := Y.presheaf.stalkSpecializes (f.base.hom.map_specializes hs) u
  have hprod : a = b * uy := by
    apply IsFractionRing.injective (Y.presheaf.stalk (f (genericPoint C))) Y.functionField
    rw [map_mul, hag, hbh, algebraMap_stalkSpecializes, heq]
    field_simp
  have hz : C.ord (f.stalkMap (genericPoint C) uy) p.1 = 0 := by
    rw [f.stalkSpecializes_stalkMap_apply (genericPoint C) p.1 hs u]
    exact order_stalk_unit p (hu.map (f.stalkMap p.1).hom)
  rw [hprod, map_mul]
  rw [C.ord_mul
    (hb.map (f.stalkMap (genericPoint C)).hom).ne_zero
    ((hu.map (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes hs)).hom).map
      (f.stalkMap (genericPoint C)).hom).ne_zero]
  rw [hz, add_zero]

end CurvePullbackLocal
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne

theorem exists_pulledCartierRepresentative {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
    [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [StalkwiseNormal Y] [CompactSpace C]
    (f : C ⟶ Y) (D : WeilDivisor Y) (hD : IsCartierDivisor D) :
    ∃ E : WeilDivisor C, IsPulledCartierRepresentative f D E := by
  classical
  choose U hU hyU g hg hDg using hD
  let y₀ : Y := f (genericPoint C)
  have hlocal (x : C) : ∃ a : Y.presheaf.stalk y₀, IsUnit a ∧
      algebraMap _ Y.functionField a = g (f x) / g y₀ := by
    exact local_equation_ratio_unit (hg (f x)) (hg y₀)
      (hDg (f x)) (hDg y₀) (image_generic_mem f (hyU (f x))) (hyU y₀)
  choose a ha heq using hlocal
  let c : PrimeDivisor C → ℤ := fun p => C.ord (f.stalkMap (genericPoint C) (a p.1)) p.1
  have hc (p : PrimeDivisor C) (x : C) (hp : f p.1 ∈ U (f x)) :
      c p = C.ord (f.stalkMap (genericPoint C) (a x)) p.1 := by
    exact curve_equation_order_eq f (hg (f p.1)) (hg (f x)) (hg y₀)
      (hDg (f p.1)) (hDg (f x)) (a p.1) (a x) (ha x)
      (heq p.1) (heq x) p (hyU (f p.1)) hp
  have ha₀ : a (genericPoint C) = 1 := by
    apply IsFractionRing.injective (Y.presheaf.stalk y₀) Y.functionField
    rw [heq, map_one]
    exact div_self (hg y₀)
  let V : C.Opens := f ⁻¹ᵁ U y₀
  have hV : (V : Set C)ᶜ ≠ Set.univ := by
    intro h
    have hm : genericPoint C ∈ (V : Set C)ᶜ := by rw [h]; trivial
    exact hm (hyU y₀)
  have hfinite : (Function.support c).Finite := by
    apply (finite_primeDivisors_in_closed V.isOpen.isClosed_compl hV).subset
    intro p hp hpV
    apply hp
    rw [hc p (genericPoint C) hpV, ha₀, map_one, order_one]
  let E : WeilDivisor C := Finsupp.ofSupportFinite c hfinite
  refine ⟨E, U y₀, hU y₀, hyU y₀, g y₀, hg y₀, hDg y₀, ?_⟩
  intro x
  refine ⟨U (f x), hU (f x), hyU (f x), g (f x), hg (f x), hDg (f x),
    a x, ha x, heq x, ?_⟩
  exact fun p hp => hc p x hp

theorem IsPulledCartierRepresentative.isCartier {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
    [IsLocallyNoetherian C] [IsLocallyNoetherian Y]
    {f : C ⟶ Y} {D : WeilDivisor Y} {E : WeilDivisor C}
    (hE : IsPulledCartierRepresentative f D E) : IsCartierDivisor E := by
  obtain ⟨_, _, _, _, _, _, hlocal⟩ := hE
  intro x
  obtain ⟨V, _, hxV, _, _, _, a, ha, _, hEa⟩ := hlocal x
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hxV)
  refine ⟨W, hW, hxW, f.stalkMap (genericPoint C) a,
    (ha.map (f.stalkMap (genericPoint C)).hom).ne_zero, ?_⟩
  exact fun p hp => hEa p (hWV hp)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory

namespace NumericalDimensionOne

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def complexProjectiveSpace (N : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)

noncomputable def projectiveConstants (N : ℕ) :
    ℂ →+* (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0) where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin (N + 1)) a⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

noncomputable def complexProjectiveSpaceMap (N : ℕ) :
    complexProjectiveSpace N ⟶ Spec (.of ℂ) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ) ≫
    Spec.map (CommRingCat.ofHom (projectiveConstants N))

def IsComplexProjective {X : Scheme} (sX : X ⟶ Spec (.of ℂ)) : Prop :=
  ∃ N : ℕ, ∃ i : X ⟶ complexProjectiveSpace N,
    IsClosedImmersion i ∧ i ≫ complexProjectiveSpaceMap N = sX

structure ComplexProjectiveVariety where
  scheme : Scheme
  structureMap : scheme ⟶ Spec (.of ℂ)
  integral : IsIntegral scheme
  connected : ConnectedSpace scheme
  projective : IsComplexProjective structureMap

attribute [instance] ComplexProjectiveVariety.integral ComplexProjectiveVariety.connected

def IsSmoothNfold (X : ComplexProjectiveVariety) (n : ℕ) : Prop :=
  SmoothOfRelativeDimension n X.structureMap

theorem projectiveConstants_bijective (N : ℕ) :
    Function.Bijective (projectiveConstants N) := by
  constructor
  · intro a b hab
    exact MvPolynomial.C_injective (Fin (N + 1)) ℂ (congrArg Subtype.val hab)
  · intro p
    refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
    exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (N + 1))).mpr p.property)).symm

theorem complexProjectiveSpace_isProper (N : ℕ) :
    IsProper (complexProjectiveSpaceMap N) := by
  let A := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ
  let : IsScalarTower ℂ (A 0) (MvPolynomial (Fin (N + 1)) ℂ) :=
    IsScalarTower.of_algebraMap_eq (R := ℂ) (S := A 0) (A := MvPolynomial (Fin (N + 1)) ℂ) fun _ => rfl
  let : Algebra.FiniteType (A 0) (MvPolynomial (Fin (N + 1)) ℂ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (A 0)
      (MvPolynomial (Fin (N + 1)) ℂ)
  let e := RingEquiv.ofBijective (projectiveConstants N) (projectiveConstants_bijective N)
  let : IsIso (CommRingCat.ofHom (projectiveConstants N)) := by
    exact e.toCommRingCatIso.isIso_hom
  have hp : IsProper (Proj.toSpecZero A) := inferInstance
  have he : IsIso (Spec.map (CommRingCat.ofHom (projectiveConstants N))) := inferInstance
  let := hp
  let := he
  change IsProper (Proj.toSpecZero A ≫
    Spec.map (CommRingCat.ofHom (projectiveConstants N)))
  let ht : IsProper (Spec.map (CommRingCat.ofHom (projectiveConstants N))) := inferInstance
  exact IsProper.comp_iff.mpr hp

theorem isProper_of_isComplexProjective {X : Scheme} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsComplexProjective sX) : IsProper sX := by
  obtain ⟨N, i, hi, rfl⟩ := hX
  let := hi
  let := complexProjectiveSpace_isProper N
  infer_instance

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors

namespace NumericalDimensionOne

theorem isIntegrallyClosed_of_etale_domain
    (R S : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S] :
    IsIntegrallyClosed S := by
  let K := FractionRing R
  let T := S ⊗[R] K
  let : Algebra K T := Algebra.TensorProduct.rightAlgebra
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  have hM : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hy))
  let : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hM
  let : Algebra.Etale K T := Algebra.Etale.of_equiv
    (Algebra.TensorProduct.commRight R K S)
  let : Module.Finite K T := Algebra.FormallyUnramified.finite_of_free K T
  let : IsArtinianRing T := .of_finite K T
  let : Field T := (IsArtinianRing.isField_of_isDomain T).toField
  have hST : Function.Injective (algebraMap S T) := IsLocalization.injective T hM
  let : IsFractionRing S T := IsLocalization.of_le (Algebra.algebraMapSubmonoid S R⁰) S⁰ hM fun x hx =>
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hST).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hx))
  apply (isIntegrallyClosed_iff T).mpr
  intro x hx
  obtain ⟨z, hz⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := K)).2
      ⟨x, hx⟩
  have hmem : ∀ z : S ⊗[R] integralClosure R K,
      ∃ s : S, algebraMap S T s = (TensorProduct.toIntegralClosure R S K z).1 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨sx, hsx⟩ := hx
      obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by simp [hsx, hsy]⟩
    | tmul s y =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral y.2
      refine ⟨s * algebraMap R S r, ?_⟩
      simp only [map_mul, TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change (s ⊗ₜ[R] (1 : K)) * (algebraMap R S r ⊗ₜ[R] (1 : K)) =
        s ⊗ₜ[R] (y : K)
      rw [← hr]
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  obtain ⟨s, hs⟩ := hmem z
  exact ⟨s, hs.trans (congrArg Subtype.val hz)⟩

theorem isIntegrallyClosed_of_smooth_field_domain
    (k S : Type*) [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] [Algebra.Smooth k S] : IsIntegrallyClosed S := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  obtain ⟨f, hfp, n, af, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  let : Algebra (MvPolynomial (Fin n) k) (Localization.Away f) := af
  let : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away f) := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away f) := he
  have hf : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
  let : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain (Localization.Away f) hf
  let : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_etale_domain (MvPolynomial (Fin n) k) (Localization.Away f)
  have hle : Submonoid.powers f ≤ p.primeCompl :=
    Submonoid.powers_le.mpr hfp
  let : Algebra (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  let : IsScalarTower S (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  let : IsLocalization (p.primeCompl.map (algebraMap S (Localization.Away f)))
      (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  apply isIntegrallyClosed_of_isLocalization (Localization.AtPrime p)
    (p.primeCompl.map (algebraMap S (Localization.Away f)))
  rintro x ⟨y, hy, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsLocalization.injective (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf))).mpr
      (fun h => hy (h ▸ p.zero_mem)))

open AlgebraicGeometry CategoryTheory
universe u

theorem integrallyClosed_stalk_of_smooth_field
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  have hs : Smooth (Spec.map φ) := hφ ▸ inferInstance
  have hs' : φ.hom.Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs
  let : Algebra k Γ(X, U) := φ.hom.toAlgebra
  let : Algebra.Smooth k Γ(X, U) := hs'
  let : IsIntegrallyClosed Γ(X, U) := isIntegrallyClosed_of_smooth_field_domain k Γ(X, U)
  let y : U := ⟨x, hxU⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := hU.isLocalization_stalk y
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    (hU.primeIdealOf y).asIdeal.primeCompl
    (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne

section TopDifferentials
variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

def alternatingRestrictScalars {M N ι : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module B M] [Module B N] [IsScalarTower A B M] [IsScalarTower A B N]
    (f : M [⋀^ι]→ₗ[B] N) : M [⋀^ι]→ₗ[A] N where
  toMultilinearMap := f.toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq

noncomputable def topDifferentialMap (n : ℕ) :
    (⋀[A]^n Ω[A⁄k]) →ₗ[A] (⋀[B]^n Ω[B⁄k]) :=
  exteriorPower.alternatingMapLinearEquiv
    ((alternatingRestrictScalars A B (exteriorPower.ιMulti B n)).compLinearMap
      (KaehlerDifferential.map k k A B))

@[simp] theorem topDifferentialMap_ιMulti (n : ℕ) (v : Fin n → Ω[A⁄k]) :
    topDifferentialMap k A B n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => KaehlerDifferential.map k k A B (v i)) := by
  simp [topDifferentialMap, alternatingRestrictScalars,
    AlternatingMap.compLinearMap_apply]
  rfl

end TopDifferentials

section SchemeScalars
universe u
variable (k : CommRingCat.{u}) {X : Scheme.{u}} [IsIntegral X]

noncomputable def schemeStalkScalar (sX : X ⟶ Spec k) (x : X) :
    k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x (by trivial)).hom.comp
    (sX.appTop.hom.comp (Scheme.ΓSpecIso k).inv.hom)

noncomputable def schemeFieldScalar (sX : X ⟶ Spec k) : k →+* X.functionField :=
  (X.germToFunctionField ⊤).hom.comp
    (sX.appTop.hom.comp (Scheme.ΓSpecIso k).inv.hom)

@[instance_reducible]
noncomputable def schemeStalkAlgebra (sX : X ⟶ Spec k) (x : X) :
    Algebra k (X.presheaf.stalk x) := (schemeStalkScalar k sX x).toAlgebra

@[instance_reducible]
noncomputable def schemeFieldAlgebra (sX : X ⟶ Spec k) : Algebra k X.functionField :=
  (schemeFieldScalar k sX).toAlgebra

theorem stalk_field_scalar_tower (sX : X ⟶ Spec k) (x : X) :
    letI := schemeStalkAlgebra k sX x
    letI := schemeFieldAlgebra k sX
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  let := schemeStalkAlgebra k sX x
  let := schemeFieldAlgebra k sX
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (X.algebraMap_germ_eq_germToFunctionField (by trivial)
    (sX.appTop ((Scheme.ΓSpecIso k).inv a))).symm

end SchemeScalars
end NumericalDimensionOne

end OAI
