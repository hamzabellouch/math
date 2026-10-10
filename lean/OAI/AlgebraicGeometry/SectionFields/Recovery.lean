import Mathlib
import OAI.AlgebraicGeometry.SectionFields.GeometricFiber

namespace OAI

/-! Complete divisorial section fields, containment and conditional recovery. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators

 

theorem exists_stalk_element_of_ord_nonneg
    (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]
    (u : X.functionField) (hu : u ≠ 0) (hord : 0 ≤ X.ord u x) :
    ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = u := by
  let : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    dvr_stalk_of_normal_codimOne X x hx
  have h : (1 : ℤᵐ⁰) ≤ Ring.ordFrac (X.presheaf.stalk x) u :=
    (X.le_ord_iff hx hu).mp hord
  rw [Ring.ordFrac_eq_valuation_inv] at h
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  exact (one_le_inv₀ (by simpa only [zero_lt_iff, Valuation.ne_zero_iff] using hu)).mp h

 
theorem exists_affine_section_of_ord_nonneg
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) (hf : f ≠ 0)
    (hord : ∀ x : X, x ∈ U → coheight x = 1 → 0 ≤ X.ord f x) :
    ∃ s : Γ(X, U), algebraMap Γ(X, U) X.functionField s = f := by
  let : IsIntegrallyClosed Γ(X, U) := integrallyClosed_affine_sections X hNormal U hU
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  apply exists_algebraMap_eq_of_mem_height_one_localizations
  intro P hP hheight
  let y : PrimeSpectrum Γ(X, U) := ⟨P, hP⟩
  let z : X := hU.fromSpec y
  have hzU : z ∈ U := (hU.isoSpec.inv y).2
  have hz : coheight z = 1 := by
    change coheight (hU.fromSpec y) = 1
    erw [coheight_eq_of_isOpenImmersion hU.fromSpec,
      ← idealHeight_eq_coheight Γ(X, U) y]
    exact hheight
  let : IsIntegrallyClosed (X.presheaf.stalk z) := hNormal z
  obtain ⟨s, hs⟩ := exists_stalk_element_of_ord_nonneg X z hz f hf (hord z hzU hz)
  let : Algebra Γ(X, U) (X.presheaf.stalk z) :=
    X.presheaf.algebra_section_stalk ⟨z, hzU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk z) P := hU.isLocalization_stalk' y hzU
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk z) X.functionField :=
    functionField_isScalarTower X U ⟨z, hzU⟩
  obtain ⟨a, b, he⟩ := IsLocalization.exists_mk'_eq P.primeCompl s
  rw [mem_localization_iff_denominator]
  refine ⟨b, b.property, ?_⟩
  rw [Submodule.mem_colon_singleton, Algebra.smul_def]
  refine ⟨a, ?_⟩
  change algebraMap Γ(X, U) X.functionField a = algebraMap Γ(X, U) X.functionField b * f
  rw [← hs, IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z) X.functionField b,
    ← map_mul, ← he, IsLocalization.mk'_spec',
    ← IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk z) X.functionField]

 
theorem exists_section_of_ord_nonneg
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (V : X.Opens) [hV : Nonempty V]
    (f : X.functionField) (hf : f ≠ 0)
    (hord : ∀ x : X, x ∈ V → coheight x = 1 → 0 ≤ X.ord f x) :
    ∃ s : Γ(X, V), algebraMap Γ(X, V) X.functionField s = f := by
  classical
  choose U hU hxU hUV using fun x : V => exists_isAffineOpen_mem_and_subset x.property
  let : ∀ x : V, Nonempty (U x) := fun x => ⟨⟨x, hxU x⟩⟩
  choose s hs using fun x : V => exists_affine_section_of_ord_nonneg X hNormal (U x) (hU x)
    f hf (fun y hy => hord y (hUV x hy))
  have hgen : ∀ x : V, genericPoint X ∈ U x := fun x =>
    ((genericPoint_spec X).mem_open_set_iff (U x).isOpen).mpr ⟨x, trivial, hxU x⟩
  have hcover : V ≤ iSup U := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro i j
    let : Nonempty ((U i ⊓ U j : X.Opens) : Set X) :=
      ⟨⟨genericPoint X, hgen i, hgen j⟩⟩
    apply @Scheme.germToFunctionField_injective X _ (U i ⊓ U j)
      ⟨⟨genericPoint X, hgen i, hgen j⟩⟩
    rw [germToFunctionField_map, germToFunctionField_map]
    exact (hs i).trans (hs j).symm
  obtain ⟨g, hg, _⟩ := X.sheaf.existsUnique_gluing' U V
    (fun x => homOfLE (hUV x)) hcover s hcompat
  refine ⟨g, ?_⟩
  let x : V := hV.some
  have he := hg x
  have he' := congrArg (X.germToFunctionField (U x)) he
  change X.germToFunctionField (U x)
    (X.presheaf.map (homOfLE (hUV x)).op g) =
      X.germToFunctionField (U x) (s x) at he'
  erw [germToFunctionField_map] at he'
  exact he'.trans (hs x)

 

theorem rational_function_descends_of_no_horizontal_poles
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (u : X.functionFieldˣ)
    (hhoriz : ∀ p : PrimeDivisor X, f p.1 = genericPoint Z →
      0 ≤ X.ord (u : X.functionField) p.1) :
    ∃ v : Z.functionFieldˣ,
      functionFieldPullback f (v : Z.functionField) = (u : X.functionField) := by
  classical
  let N := (principalDivisor X u).filter (fun p => X.ord (u : X.functionField) p.1 < 0)
  have hN : IsVerticalDivisor f N := by
    intro p hp hgen
    apply hp
    simp [N, not_lt.mpr (hhoriz p hgen)]
  obtain ⟨U, hgen, hU⟩ := exists_open_avoiding_vertical_divisor f N hN
  let : Nonempty U := ⟨⟨genericPoint Z, hgen⟩⟩
  obtain ⟨s, hs⟩ := exists_section_of_ord_nonneg X hNormal (f ⁻¹ᵁ U)
    (u : X.functionField) (Units.ne_zero u) (by
      intro x hx hcodim
      have he := hU ⟨x, hcodim⟩ hx
      by_contra hn
      have hn' : X.ord (u : X.functionField) x < 0 := lt_of_not_ge hn
      have he' : X.ord (u : X.functionField) x = 0 := by simpa [N, hn'] using he
      exact hn'.ne he')
  let t : Γ(Z, U) := inv (f.app U) s
  have ht : f.app U t = s := by
    exact congrArg (fun g => g s) (IsIso.inv_hom_id (f.app U))
  have he : functionFieldPullback f (Z.germToFunctionField U t) = (u : X.functionField) := by
    rw [functionFieldPullback_germ, ht]
    exact hs
  have hv : Z.germToFunctionField U t ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [← he, h, map_zero]
  exact ⟨Units.mk0 (Z.germToFunctionField U t) hv, he⟩

 

 

def divisorialSections (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (A : RationalWeilDivisor X) : Set X.functionFieldˣ :=
  { u | ∀ p : PrimeDivisor X, 0 ≤ X.ord (u : X.functionField) p.1 + ⌊A p⌋ }

 
def sectionField (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (A : RationalWeilDivisor X) : Subfield X.functionField :=
  Subfield.closure { t | ∃ u ∈ divisorialSections X A, ∃ v ∈ divisorialSections X A,
    t = (u : X.functionField) / (v : X.functionField) }

 

theorem mem_divisorialSections_iff
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (A : RationalWeilDivisor X) (u : X.functionFieldˣ) :
    u ∈ divisorialSections X A ↔
      ∀ p : PrimeDivisor X, 0 ≤ A p + (X.ord (u : X.functionField) p.1 : ℚ) := by
  unfold divisorialSections
  change (∀ p, _) ↔ _
  apply forall_congr'
  intro p
  constructor
  · intro h
    have hi : -X.ord (u : X.functionField) p.1 ≤ ⌊A p⌋ := by omega
    have hq := Int.le_floor.mp hi
    push_cast at hq
    linarith
  · intro h
    have hq : ((-X.ord (u : X.functionField) p.1 : ℤ) : ℚ) ≤ A p := by
      push_cast
      linarith
    have hi := Int.le_floor.mpr hq
    omega

theorem mul_mem_divisorialSections
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    {A B : RationalWeilDivisor X} {u v : X.functionFieldˣ}
    (hu : u ∈ divisorialSections X A) (hv : v ∈ divisorialSections X B) :
    u * v ∈ divisorialSections X (A + B) := by
  rw [mem_divisorialSections_iff] at hu hv ⊢
  intro p
  have h := add_nonneg (hu p) (hv p)
  simpa only [Finsupp.add_apply, Units.val_mul, X.ord_mul (Units.ne_zero u) (Units.ne_zero v),
    Int.cast_add] using (by linarith : 0 ≤ A p + B p + ((X.ord (u : X.functionField) p.1 : ℚ) +
      (X.ord (v : X.functionField) p.1 : ℚ)))

theorem pow_mem_divisorialSections
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    {A : RationalWeilDivisor X} {u : X.functionFieldˣ}
    (hu : u ∈ divisorialSections X A) (n : ℕ) :
    u ^ n ∈ divisorialSections X ((n : ℚ) • A) := by
  rw [mem_divisorialSections_iff] at hu ⊢
  intro p
  simpa only [Finsupp.smul_apply, smul_eq_mul, Units.val_pow_eq_pow_val,
    ord_pow X _ (Units.ne_zero u), Int.cast_mul, Int.cast_natCast, mul_add]
    using mul_nonneg (Nat.cast_nonneg n : (0 : ℚ) ≤ n) (hu p)

 

theorem sectionField_le_positive_multiple
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (A : RationalWeilDivisor X) (n : ℕ) (hn : 0 < n) :
    sectionField X A ≤ sectionField X ((n : ℚ) • A) := by
  apply Subfield.closure_le.mpr
  rintro t ⟨u, hu, v, hv, rfl⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hA : ((k + 1 : ℕ) : ℚ) • A = A + (k : ℚ) • A := by
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_comm]
  apply Subfield.subset_closure
  refine ⟨u * v ^ k, ?_, v * v ^ k, ?_, ?_⟩
  · rw [hA]
    exact mul_mem_divisorialSections X hu (pow_mem_divisorialSections X hv k)
  · rw [hA]
    exact mul_mem_divisorialSections X hv (pow_mem_divisorialSections X hv k)
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [mul_div_mul_right _ _ (pow_ne_zero _ (Units.ne_zero v))]

theorem divisorialSections_nonempty_positive_multiple
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (A : RationalWeilDivisor X) (n : ℕ)
    (h : (divisorialSections X A).Nonempty) :
    (divisorialSections X ((n : ℚ) • A)).Nonempty := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u ^ n, pow_mem_divisorialSections X hu n⟩

 
theorem ord_nonneg_of_section
    (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (U : X.Opens) [Nonempty U] (s : Γ(X, U)) (hs : s ≠ 0)
    (x : X) (hx : x ∈ U) : 0 ≤ X.ord (X.germToFunctionField U s) x := by
  simpa only [Algebra.smul_def, mul_one, ord_one, RingHom.algebraMap_toAlgebra]
    using X.ord_le_smul hx hs (1 : X.functionField)

 

theorem pullbackQCartier_effective
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (heff : ∀ p : PrimeDivisor Z, 0 ≤ D p) :
    ∀ p : PrimeDivisor X, 0 ≤ pullbackQCartier hNormal f D hD p := by
  intro p
  let c := hD.data
  let U := c.chart (f p.1)
  let : Nonempty U := ⟨⟨f p.1, c.mem_chart (f p.1)⟩⟩
  let u := c.equation (f p.1)
  obtain ⟨s, hs⟩ := exists_section_of_ord_nonneg Z hNormal U
    (u : Z.functionField) (Units.ne_zero u) (by
      intro z hz hcodim
      have heq := c.ord_eq (f p.1) ⟨z, hcodim⟩ hz
      have hq : (0 : ℚ) ≤ (Z.ord (u : Z.functionField) z : ℚ) := by
        rw [← heq]
        exact mul_nonneg (Nat.cast_nonneg _) (heff _)
      exact_mod_cast hq)
  change Z.germToFunctionField U s = (u : Z.functionField) at hs
  have hnz : functionFieldPullback f (u : Z.functionField) ≠ 0 := by
    exact (map_ne_zero (functionFieldPullback f)).mpr (Units.ne_zero u)
  have hbs : f.app U s ≠ 0 := by
    intro hz
    apply hnz
    rw [← hs, functionFieldPullback_germ, hz, map_zero]
  have hnonneg := ord_nonneg_of_section X (f ⁻¹ᵁ U) (f.app U s) hbs p.1 (c.mem_chart _)
  rw [← functionFieldPullback_germ, hs] at hnonneg
  change 0 ≤ (X.ord (functionFieldPullback f (u : Z.functionField)) p.1 : ℚ) / c.index
  exact div_nonneg (by exact_mod_cast hnonneg) (Nat.cast_nonneg _)

 

theorem pullback_mem_divisorialSections
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (v : Z.functionFieldˣ) (hv : v ∈ divisorialSections Z D) :
    Units.map (functionFieldPullback f).toMonoidHom v ∈
      divisorialSections X (pullbackQCartier hNormal f D hD) := by
  rw [mem_divisorialSections_iff] at hv ⊢
  have hpr := isQCartier_principal Z v
  have hsum := isQCartier_add hD hpr
  have heff := pullbackQCartier_effective hNormal f
    (D + rationalPrincipalDivisor Z v) hsum (by
      intro p
      simpa using hv p)
  rw [pullbackQCartier_add hNormal f hD hpr hsum,
    pullbackQCartier_principal hNormal f v hpr] at heff
  exact heff

 

theorem lift_section_of_exact_presentation
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (χ : X.functionFieldˣ)
    (heq : A + rationalPrincipalDivisor X χ = pullbackQCartier hNZ f D hD)
    (v : Z.functionFieldˣ) (hv : v ∈ divisorialSections Z D) :
    χ * Units.map (functionFieldPullback f).toMonoidHom v ∈ divisorialSections X A := by
  have h := pullback_mem_divisorialSections hNZ f D hD v hv
  rw [← heq, mem_divisorialSections_iff] at h
  rw [mem_divisorialSections_iff]
  intro p
  simpa only [Finsupp.add_apply, rationalPrincipalDivisor_apply,
    Units.val_mul, X.ord_mul (Units.ne_zero χ) (Units.ne_zero _), Int.cast_add, add_assoc]
    using h p

 

theorem section_quotient_descends_of_exact_presentation
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (χ : X.functionFieldˣ)
    (heq : A + rationalPrincipalDivisor X χ = pullbackQCartier hNZ f D hD)
    (u : X.functionFieldˣ) (hu : u ∈ divisorialSections X A) :
    ∃ v : Z.functionFieldˣ,
      functionFieldPullback f (v : Z.functionField) = ((u / χ : X.functionFieldˣ) : X.functionField) := by
  apply rational_function_descends_of_no_horizontal_poles hNX f (u / χ)
  intro p hgen
  have hzero : pullbackQCartier hNZ f D hD p = 0 := by
    by_contra hn
    exact isVertical_pullbackQCartier hNZ f D hD p hn hgen
  have hp := congrArg (fun B : RationalWeilDivisor X => B p) heq
  simp only [Finsupp.add_apply, rationalPrincipalDivisor_apply, hzero] at hp
  have hu' := (mem_divisorialSections_iff X A u).mp hu p
  have hord : (0 : ℚ) ≤ (X.ord (u : X.functionField) p.1 : ℚ) -
      (X.ord (χ : X.functionField) p.1 : ℚ) := by linarith
  simp only [Units.val_div_eq_div_val, ord_div X _ _ (Units.ne_zero u) (Units.ne_zero χ)]
  exact_mod_cast hord

 

theorem sectionField_le_base_of_exact_presentation
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (χ : X.functionFieldˣ)
    (heq : A + rationalPrincipalDivisor X χ = pullbackQCartier hNZ f D hD) :
    sectionField X A ≤ (functionFieldPullback f).fieldRange := by
  apply Subfield.closure_le.mpr
  rintro t ⟨u, hu, v, hv, rfl⟩
  obtain ⟨a, ha⟩ := section_quotient_descends_of_exact_presentation
    hNX hNZ f A D hD χ heq u hu
  obtain ⟨b, hb⟩ := section_quotient_descends_of_exact_presentation
    hNX hNZ f A D hD χ heq v hv
  apply RingHom.mem_fieldRange.mpr
  refine ⟨(a : Z.functionField) / (b : Z.functionField), ?_⟩
  rw [map_div₀, ha, hb]
  simp only [Units.val_div_eq_div_val]
  exact div_div_div_cancel_right₀ (Units.ne_zero χ) _ _

 

theorem base_sectionField_le_of_exact_presentation
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (χ : X.functionFieldˣ)
    (heq : A + rationalPrincipalDivisor X χ = pullbackQCartier hNZ f D hD) :
    (sectionField Z D).map (functionFieldPullback f) ≤ sectionField X A := by
  apply Subfield.map_le_iff_le_comap.mpr
  apply Subfield.closure_le.mpr
  rintro t ⟨u, hu, v, hv, rfl⟩
  change functionFieldPullback f ((u : Z.functionField) / (v : Z.functionField)) ∈ sectionField X A
  rw [map_div₀]
  apply Subfield.subset_closure
  refine ⟨χ * Units.map (functionFieldPullback f).toMonoidHom u,
    lift_section_of_exact_presentation hNZ f A D hD χ heq u hu,
    χ * Units.map (functionFieldPullback f).toMonoidHom v,
    lift_section_of_exact_presentation hNZ f A D hD χ heq v hv, ?_⟩
  simp only [Units.val_mul, Units.coe_map]
  rw [mul_div_mul_left _ _ (Units.ne_zero χ)]
  rfl

 

theorem sectionField_eq_base_of_exact_presentation
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (χ : X.functionFieldˣ)
    (heq : A + rationalPrincipalDivisor X χ = pullbackQCartier hNZ f D hD)
    (hne : (divisorialSections Z D).Nonempty)
    (hfield : sectionField Z D = ⊤) :
    (divisorialSections X A).Nonempty ∧
      sectionField X A = (functionFieldPullback f).fieldRange := by
  constructor
  · obtain ⟨v, hv⟩ := hne
    exact ⟨_, lift_section_of_exact_presentation hNZ f A D hD χ heq v hv⟩
  · apply le_antisymm
    · exact sectionField_le_base_of_exact_presentation hNX hNZ f A D hD χ heq
    · have h := base_sectionField_le_of_exact_presentation hNZ f A D hD χ heq
      rwa [hfield, ← RingHom.fieldRange_eq_map] at h

 

theorem positive_multiple_exact_presentation
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (p : ℕ) (hp : 0 < p) (ψ : X.functionFieldˣ)
    (heq : A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hNZ f D hD)
    (l : ℕ) (hpl : p ∣ l) :
    ∃ χ : X.functionFieldˣ,
      (l : ℚ) • A + rationalPrincipalDivisor X χ =
        pullbackQCartier hNZ f ((l : ℚ) • D) (isQCartier_smul hD (l : ℚ)) := by
  obtain ⟨k, rfl⟩ := hpl
  refine ⟨ψ ^ k, ?_⟩
  rw [pullbackQCartier_smul hNZ f hD, ← heq,
    rationalPrincipalDivisor_pow, smul_add, smul_smul]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hscalar : (k : ℚ) = ((p * k : ℕ) : ℚ) * (p : ℚ)⁻¹ := by
    rw [Nat.cast_mul]
    field_simp
  rw [← hscalar]

 

theorem multiples_recover_base_of_exact_presentation_and_base_system
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (p : ℕ) (hp : 0 < p) (ψ : X.functionFieldˣ)
    (heq : A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hNZ f D hD)
    (s : ℕ) (hps : p ∣ s)
    (hne : (divisorialSections Z ((s : ℚ) • D)).Nonempty)
    (hfield : sectionField Z ((s : ℚ) • D) = ⊤) :
    ∀ l : ℕ, 0 < l → s ∣ l →
      (divisorialSections X ((l : ℚ) • A)).Nonempty ∧
      sectionField X ((l : ℚ) • A) = (functionFieldPullback f).fieldRange := by
  intro l hl hsl
  obtain ⟨k, hk⟩ := hsl
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hn
    simp [hk, hk0] at hl
  have hequiv : (l : ℚ) • D = (k : ℚ) • ((s : ℚ) • D) := by
    rw [hk, smul_smul, Nat.cast_mul, mul_comm]
  have hne' : (divisorialSections Z ((l : ℚ) • D)).Nonempty := by
    rw [hequiv]
    exact divisorialSections_nonempty_positive_multiple Z ((s : ℚ) • D) k hne
  have hfield' : sectionField Z ((l : ℚ) • D) = ⊤ := by
    apply top_unique
    rw [← hfield]
    rw [hequiv]
    exact sectionField_le_positive_multiple Z ((s : ℚ) • D) k hkpos
  obtain ⟨χ, hχ⟩ := positive_multiple_exact_presentation hNZ f A D hD p hp ψ heq l
    (dvd_trans hps ⟨k, hk⟩)
  exact sectionField_eq_base_of_exact_presentation hNX hNZ f ((l : ℚ) • A)
    ((l : ℚ) • D) (isQCartier_smul hD (l : ℚ)) χ hχ hne' hfield'

 

def allDegreeSectionField (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (A : RationalWeilDivisor X) : Subfield X.functionField :=
  ⨆ n : ℕ+, sectionField X (((n : ℕ) : ℚ) • A)

 

theorem sectionField_le_base_of_rational_presentation
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (p : ℕ) (hp : 0 < p) (ψ : X.functionFieldˣ)
    (heq : A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hNZ f D hD)
    (n : ℕ) :
    sectionField X ((n : ℚ) • A) ≤ (functionFieldPullback f).fieldRange := by
  apply (sectionField_le_positive_multiple X ((n : ℚ) • A) p hp).trans
  rw [smul_smul, ← Nat.cast_mul]
  obtain ⟨χ, hχ⟩ := positive_multiple_exact_presentation hNZ f A D hD p hp ψ heq
    (p * n) (dvd_mul_right p n)
  exact sectionField_le_base_of_exact_presentation hNX hNZ f _ _
    (isQCartier_smul hD ((p * n : ℕ) : ℚ)) χ hχ

 

theorem sectionField_le_base_of_rationallyLinearlyEquivalent_pullback
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hlinear : RationallyLinearlyEquivalent X A (pullbackQCartier hNZ f D hD))
    (n : ℕ) :
    sectionField X ((n : ℚ) • A) ≤ (functionFieldPullback f).fieldRange := by
  obtain ⟨p, hp, ψ, hψ⟩ := hlinear
  have heq : A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ⁻¹ =
      pullbackQCartier hNZ f D hD := by
    rw [rationalPrincipalDivisor_inv, ← hψ, smul_neg, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hp.ne'), one_smul]
    abel
  exact sectionField_le_base_of_rational_presentation hNX hNZ f A D hD p hp ψ⁻¹ heq n

 

theorem allDegreeSectionField_le_base_of_rationallyLinearlyEquivalent_pullback
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hlinear : RationallyLinearlyEquivalent X A (pullbackQCartier hNZ f D hD)) :
    allDegreeSectionField X A ≤ (functionFieldPullback f).fieldRange := by
  apply iSup_le
  intro n
  exact sectionField_le_base_of_rationallyLinearlyEquivalent_pullback hNX hNZ f A D hD
    hlinear n

 

theorem allDegreeSectionField_eq_base_of_exact_presentation_and_base_system
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (p : ℕ) (hp : 0 < p) (ψ : X.functionFieldˣ)
    (heq : A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hNZ f D hD)
    (s : ℕ) (hs : 0 < s) (hps : p ∣ s)
    (hne : (divisorialSections Z ((s : ℚ) • D)).Nonempty)
    (hfield : sectionField Z ((s : ℚ) • D) = ⊤) :
    allDegreeSectionField X A = (functionFieldPullback f).fieldRange := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact sectionField_le_base_of_rational_presentation hNX hNZ f A D hD p hp ψ heq n
  · have h :=
      (multiples_recover_base_of_exact_presentation_and_base_system hNX hNZ f A D hD
        p hp ψ heq s hps hne hfield s hs dvd_rfl).2
    rw [← h]
    exact le_iSup (fun n : ℕ+ => sectionField X (((n : ℕ) : ℚ) • A)) ⟨s, hs⟩

end RelativeDenominators
end

end OAI
