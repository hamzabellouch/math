import OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder
import OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.LocalSectionOrder PiExponent.CurveLocalOrder
open scoped BigOperators

namespace PiExponent.WeightedSectionOrder


theorem coefficient_tilde_end {A : Type} [CommRing A] (f : A →ₗ[A] A) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (endValue (tildeSelf.inv ≫
        (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f) ≫ tildeSelf.hom)) = f 1 := by
  have h := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (R := CommRingCat.of A) (ModuleCat.ofHom f) ⊤) (1 : A)
  change ((tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f)).app ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv 1) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (f 1) at h
  rw [map_one] at h
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (((tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f)).app ⊤ (1 : Γ(Spec (CommRingCat.of A), ⊤))) = f 1
  rw [h]
  simp

variable {A K : Type} {ι : Type*} [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]

def coordinateBasis (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    A ≃ₗ[A] generatedLattice A y s :=
  LinearEquiv.ofBijective (generatedSectionMap y s a ha)
    (generatedSectionMap_bijective_of_span y s a ha hya hspan)

def coordinateFrame (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    generatedSheaf (A := A) y s ≅ O (Spec (CommRingCat.of A)) :=
  (tilde.functor (CommRingCat.of A)).mapIso
    (coordinateBasis y s a ha hya hspan).symm.toModuleIso ≪≫ tildeSelf

theorem coordinate_coefficient (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) :
    localCoefficient (coordinateFrame y s a ha hya hspan) (generatedSection y s b hb) =
      (coordinateBasis y s a ha hya hspan).symm
        ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩ := by
  unfold localCoefficient coefficient coordinateFrame generatedSection
  erw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp_assoc]
  have h := coefficient_tilde_end
    ((coordinateBasis y s a ha hya hspan).symm.toLinearMap.comp
      (generatedSectionMap y s b hb))
  simp only [LinearMap.comp_apply] at h
  simp [generatedSectionMap] at h
  exact h

theorem coordinate_coefficient_image (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) :
    algebraMap A K (localCoefficient (coordinateFrame y s a ha hya hspan)
      (generatedSection y s b hb)) = y b / y a := by
  rw [coordinate_coefficient, eq_div_iff hya]
  have h := (coordinateBasis y s a ha hya hspan).apply_symm_apply
    ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩
  have hh := congrArg (fun z : generatedLattice A y s => (z : K)) h
  change (coordinateBasis y s a ha hya hspan).symm
    ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩ • y a = y b at hh
  simpa only [Algebra.smul_def] using hh

theorem coordinate_coefficient_ne_zero (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) (hyb : y b ≠ 0) :
    localCoefficient (coordinateFrame y s a ha hya hspan) (generatedSection y s b hb) ≠ 0 := by
  intro h
  have hr := coordinate_coefficient_image y s a ha hya hspan b hb
  rw [h, map_zero] at hr
  exact div_ne_zero hyb hya hr.symm

def sectionZeroEuler [Algebra ℂ A]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A))) (t : O (Spec (CommRingCat.of A)) ⟶ M)
    (d : ℕ) : ℤ :=
  eulerCharacteristic (CurveZeroEuler.algebraStructureMap
    (A ⧸ Ideal.span {localCoefficient e t})) d (structureSheaf (zeroScheme e t))

theorem coordinate_zero_euler_eq_order_difference
    [IsDiscreteValuationRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) (hyb : y b ≠ 0) (d : ℕ) :
    sectionZeroEuler (A := A) (coordinateFrame y s a ha hya hspan)
      (generatedSection y s b hb) d =
      WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y b) -
        WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y a) := by
  let c := localCoefficient (coordinateFrame y s a ha hya hspan) (generatedSection y s b hb)
  have hc : c ≠ 0 := coordinate_coefficient_ne_zero y s a ha hya hspan b hb hyb
  change eulerCharacteristic (CurveZeroEuler.algebraStructureMap (A ⧸ Ideal.span {c})) d
    (structureSheaf (Spec (CommRingCat.of (A ⧸ Ideal.span {c})))) = _
  rw [CurveZeroEuler.principal_zero_euler_eq_order hc]
  have hi := integerOrder_field_image_eq_length (K := K) hc
  have hu : Units.mk0 (algebraMap A K c)
      ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hc) =
      Units.mk0 (y b) hyb / Units.mk0 (y a) hya := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mk0]
    exact coordinate_coefficient_image y s a ha hya hspan b hb
  rw [hu, WeightedCurveDegree.integerOrder_div, length_quotient_span_eq_addVal hc] at hi
  simpa only [WeightedPolynomialPole.coordinateOrder, dite_eq_right hyb, dite_eq_right hya] using hi.symm

theorem exists_constant_section_zero_euler_eq_weighted_pole
    [IsDiscreteValuationRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)] [Fintype ι] [DecidableEq ι]
    (x : ι → K) (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (M : Finset (ι → ℕ)) (hzero : 0 ∈ M)
    (hpure : ∀ i, Pi.single i (powers i) ∈ M)
    (hbudget : ∀ a ∈ M, (∑ i, w i * (a i : ℚ)) ≤ R) (d : ℕ) :
    let y : (ι → ℕ) → K := fun a => ∏ i, x i ^ a i
    let t : O (Spec (CommRingCat.of A)) ⟶ generatedSheaf (A := A) y M :=
      generatedSection (A := A) y M 0 hzero
    ∃ e : generatedSheaf (A := A) y M ≅ O (Spec (CommRingCat.of A)),
      t ≠ 0 ∧
      (sectionZeroEuler (A := A) (M := generatedSheaf (A := A) y M) e t d : ℚ) =
      R * WeightedPolynomialPole.coordinatePole (fractionAddValuation A K) x w := by
  dsimp only
  obtain ⟨a, ha, hya, hao, hmin⟩ := WeightedMonomialPole.exists_minimizing_monomial
    (fractionAddValuation A K) x w hw hR powers hpowers M hzero hpure hbudget
  let y : (ι → ℕ) → K := fun b => ∏ i, x i ^ b i
  have hspan : generatedLattice A y M = Submodule.span A {y a} :=
    generatedLattice_eq_span_of_minimum y M a ha hya hmin
  let e := coordinateFrame y M a ha hya hspan
  have hyzero : y 0 ≠ 0 := by simp [y]
  refine ⟨e, (localCoefficient_eq_zero_iff e _).not.mp
    (coordinate_coefficient_ne_zero y M a ha hya hspan 0 hzero hyzero), ?_⟩
  have h := coordinate_zero_euler_eq_order_difference y M a ha hya hspan 0 hzero hyzero d
  have hz : WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y 0) = 0 := by
    simp [y, WeightedPolynomialPole.coordinateOrder]
  rw [hz, zero_sub] at h
  change _ = R * WeightedPolynomialPole.coordinatePole (fractionAddValuation A K) x w
  rw [show e = coordinateFrame y M a ha hya hspan from rfl, h]
  push_cast
  exact neg_eq_iff_eq_neg.mpr (by simpa [y] using hao)

end PiExponent.WeightedSectionOrder

end

end OAI
