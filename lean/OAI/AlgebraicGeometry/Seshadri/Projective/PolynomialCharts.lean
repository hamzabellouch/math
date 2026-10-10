import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.IntegralSubschemes

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] Classical.propDecidable

lemma homogeneous_eval₂_scale {R S σ : Type*} [CommRing R] [CommRing S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (u : σ → S) (a : S) :
    eval₂ f (fun j => a * u j) p = a ^ n * eval₂ f u p := by
  classical
  rw [p.as_sum]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hd]
  ring

variable {R σ : Type*} [CommRing R] (i : σ)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev PolyGrade (R σ : Type*) [CommRing R] := MvPolynomial.homogeneousSubmodule σ R
lemma poly_X_mem : X (R := R) i ∈ PolyGrade R σ 1 := isHomogeneous_X R i

abbrev PolyChart := HomogeneousLocalization.Away (PolyGrade R σ) (X i)
abbrev ChartVariables := {j : σ // j ≠ i}

def chartConstants : R →+* PolyChart (R := R) i :=
  (HomogeneousLocalization.fromZeroRingHom _ _).comp
    { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
      map_one' := Subtype.ext C_1
      map_mul' := fun _ _ => Subtype.ext C_mul
      map_zero' := Subtype.ext C_0
      map_add' := fun _ _ => Subtype.ext C_add }

def chartCoordinate (j : σ) : PolyChart (R := R) i :=
  Away.mk _ (poly_X_mem (R := R) i) 1 (X j) (by simpa using poly_X_mem (R := R) j)

def dehomogenize : MvPolynomial σ R →+* MvPolynomial (ChartVariables i) R :=
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

@[simp] lemma dehomogenize_X_self : dehomogenize (R := R) i (X i) = 1 := by
  classical
  simp [dehomogenize]

def chartToPoly : PolyChart (R := R) i →+* MvPolynomial (ChartVariables i) R :=
  (Localization.awayLift (dehomogenize i) (X i) (by simp)).comp (algebraMap _ _)

def polyToChart : MvPolynomial (ChartVariables i) R →+* PolyChart (R := R) i :=
  eval₂Hom (chartConstants i) (fun j => chartCoordinate i j.val)

@[simp] lemma chartToPoly_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    chartToPoly i (Away.mk _ (poly_X_mem (R := R) i) n p hp) = dehomogenize i p := by
  have h := Localization.awayLift_mk (dehomogenize (R := R) i) (X i) p 1
    (by simp) n
  simpa only [chartToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, one_pow, mul_one] using h

@[simp] lemma chartToPoly_constants (r : R) :
    chartToPoly i (chartConstants i r) = C r := by
  exact (chartToPoly_mk i 0 (C r) (by simp)).trans
    (by simp [dehomogenize])

@[simp] lemma chartToPoly_coordinate (j : σ) :
    chartToPoly (R := R) i (chartCoordinate i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  rw [chartCoordinate, chartToPoly_mk]
  simp [dehomogenize]

lemma chartToPoly_comp_polyToChart :
    (chartToPoly (R := R) i).comp (polyToChart i) = RingHom.id _ := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [polyToChart]
  · intro j
    simp [polyToChart, j.property]

lemma chart_val_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    (Away.mk _ (poly_X_mem (R := R) i) n p hp).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) p *
        (IsLocalization.Away.invSelf (X (R := R) i)) ^ n := by
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  rw [IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow]
  simp only [one_pow]
  rfl

lemma chart_val_constants (r : R) :
    (chartConstants i r).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (C r) := by
  exact (chart_val_mk i 0 (C r) (by simp)).trans
    (by simp only [pow_zero, mul_one])

lemma chart_val_coordinate (j : σ) :
    (chartCoordinate (R := R) i j).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j) *
        IsLocalization.Away.invSelf (X (R := R) i) := by
  rw [chartCoordinate, chart_val_mk, pow_one]

lemma chart_dehomogenize_val :
    (algebraMap (PolyChart (R := R) i) (Localization.Away (X i))).comp
      ((polyToChart i).comp (dehomogenize i)) =
    eval₂Hom ((algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))).comp C)
      (fun j => IsLocalization.Away.invSelf (X (R := R) i) *
        algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [dehomogenize, polyToChart, chart_val_constants]
  · intro j
    by_cases h : j = i
    · subst j
      simp only [RingHom.comp_apply, dehomogenize_X_self, map_one, eval₂Hom_X']
      symm
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf (X i)
    · simp [dehomogenize, polyToChart, h, chart_val_coordinate, mul_comm]

lemma polyToChart_comp_chartToPoly :
    (polyToChart (R := R) i).comp (chartToPoly i) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (poly_X_mem (R := R) i) x
  apply HomogeneousLocalization.val_injective _
  simp only [RingHom.comp_apply, RingHom.id_apply, chartToPoly_mk, chart_val_mk]
  have he := RingHom.congr_fun (chart_dehomogenize_val (R := R) i) p
  change (polyToChart i (dehomogenize i p)).val = _ at he
  rw [he]
  change eval₂ _ _ p = _
  rw [homogeneous_eval₂_scale (by simpa using hp)]
  have hid : eval₂Hom ((algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))).comp C)
      (fun j => algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j)) =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp
  change _ * (eval₂Hom _ _ p) = _
  rw [hid]
  exact mul_comm _ _

def polynomialChartEquiv : PolyChart (R := R) i ≃+* MvPolynomial (ChartVariables i) R :=
  { chartToPoly i with
    invFun := polyToChart i
    left_inv := fun p => RingHom.congr_fun (polyToChart_comp_chartToPoly i) p
    right_inv := fun p => RingHom.congr_fun (chartToPoly_comp_polyToChart i) p }

def projectiveChartIso :
    (Proj.basicOpen (PolyGrade R σ) (X i)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (ChartVariables i) R)) :=
  Proj.basicOpenIsoSpec _ (X i) (poly_X_mem (R := R) i) (by decide) ≪≫
    Scheme.Spec.mapIso ((polynomialChartEquiv i).toCommRingCatIso.symm.op)

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] [Fintype σ]

def linearEquation (t : σ → R) : MvPolynomial σ R := ∑ i, C (t i) * X i

lemma linearEquation_homogeneous (t : σ → R) :
    linearEquation t ∈ PolyGrade R σ 1 := by
  exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ _)

lemma linearEquation_chart (t : σ → R) (i : σ) :
    Away.isLocalizationElem (poly_X_mem (R := R) i) (linearEquation_homogeneous t) =
      ∑ j, chartConstants i (t j) * chartCoordinate i j := by
  apply HomogeneousLocalization.val_injective _
  change (Away.mk _ _ 1 _ _).val = _
  rw [chart_val_mk]
  rw [← HomogeneousLocalization.algebraMap_apply]
  simp only [linearEquation, map_sum, map_mul, pow_one,
    HomogeneousLocalization.algebraMap_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [chart_val_constants, chart_val_coordinate]
  exact mul_assoc _ _ _

lemma hyperplane_chart_preimage (t : σ → R) (i : σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (linearEquation t) =
      PrimeSpectrum.basicOpen (∑ j, chartConstants i (t j) * chartCoordinate i j) := by
  rw [Proj.awayι_preimage_basicOpen _ _ (by decide) (linearEquation_homogeneous t)
    (by decide), linearEquation_chart]

omit [Fintype σ] in
lemma chartCoordinate_self (i : σ) : chartCoordinate (R := R) i i = 1 := by
  apply HomogeneousLocalization.val_injective _
  rw [chart_val_coordinate, HomogeneousLocalization.val_one]
  exact IsLocalization.Away.mul_invSelf (X i)

lemma hyperplane_affine_preimage {Y : Scheme} (h : Y ⟶ Proj (PolyGrade R σ))
    (U : Y.affineOpens) (i : σ) (φ : PolyChart (R := R) i →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) = U.2.fromSpec ≫ h)
    (t : σ → R) :
    U.2.fromSpec ⁻¹ᵁ (h ⁻¹ᵁ Proj.basicOpen (PolyGrade R σ) (linearEquation t)) =
      PrimeSpectrum.basicOpen (∑ j, φ (chartConstants i (t j)) * φ (chartCoordinate i j)) := by
  rw [← Scheme.Hom.comp_preimage, ← hφ, Scheme.Hom.comp_preimage,
    hyperplane_chart_preimage]
  ext x
  change φ (∑ j, chartConstants i (t j) * chartCoordinate i j) ∉ x.asIdeal ↔
    (∑ j, φ (chartConstants i (t j)) * φ (chartCoordinate i j)) ∉ x.asIdeal
  simp only [map_sum, map_mul]

lemma hyperplane_affine_preimage_reindexed {K : Type} [Field K] {n : ℕ}
    {Y : Scheme} (h : Y ⟶ Proj (PolyGrade K (Option (Fin n))))
    (U : Y.affineOpens) [Algebra K Γ(Y, U.1)]
    (e : Option (Fin n) ≃ Option (Fin n))
    (φ : PolyChart (R := K) (e none) →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option (Fin n))) (X (e none)) (poly_X_mem (e none))
        (by decide) = U.2.fromSpec ≫ h)
    (hK : ∀ c, φ (chartConstants (e none) c) = algebraMap K Γ(Y, U.1) c)
    (t : Option (Fin n) → K) :
    U.2.fromSpec ⁻¹ᵁ (h ⁻¹ᵁ Proj.basicOpen (PolyGrade K (Option (Fin n)))
      (linearEquation t)) = PrimeSpectrum.basicOpen
        (algebraMap K Γ(Y, U.1) (t (e none)) -
          ∑ j, algebraMap K Γ(Y, U.1) (t (e (some j))) *
            (-φ (chartCoordinate (e none) (e (some j))))) := by
  rw [hyperplane_affine_preimage h U (e none) φ hφ]
  congr 1
  rw [← e.sum_comp]
  simp only [Fintype.sum_option, hK, chartCoordinate_self, map_one, mul_one,
    mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

omit [Fintype σ] in

theorem projective_affine_factor {Y : Scheme} (h : Y ⟶ Proj (PolyGrade R σ))
    (U : Y.affineOpens) (i : σ)
    (hU : U.1 ≤ h ⁻¹ᵁ Proj.basicOpen (PolyGrade R σ) (X i)) :
    ∃ φ : PolyChart (R := R) i →+* Γ(Y, U.1),
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) = U.2.fromSpec ≫ h := by
  let f := Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)
  have hRange : Set.range (U.2.fromSpec ≫ h) ⊆ Set.range f := by
    rintro _ ⟨x, rfl⟩
    have hx : U.2.fromSpec x ∈ U.1 := by
      have hx := Set.mem_range_self (f := U.2.fromSpec) x
      rw [U.2.range_fromSpec] at hx
      exact hx
    have hh := hU hx
    change h (U.2.fromSpec x) ∈ Proj.basicOpen (PolyGrade R σ) (X i) at hh
    change h (U.2.fromSpec x) ∈ Set.range f
    have he : f.opensRange = Proj.basicOpen (PolyGrade R σ) (X i) :=
      Proj.opensRange_awayι _ _ _ _
    rw [← he] at hh
    exact hh
  let l := IsOpenImmersion.lift f (U.2.fromSpec ≫ h) hRange
  refine ⟨(Spec.preimage l).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac f (U.2.fromSpec ≫ h) hRange

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R σ : Type u} [CommRing R] [Fintype σ]

omit [Fintype σ] in
                                                     
def projectiveConstants : R →+* PolyGrade R σ 0 :=
  { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
    map_one' := Subtype.ext C_1
    map_mul' := fun _ _ => Subtype.ext C_mul
    map_zero' := Subtype.ext C_0
    map_add' := fun _ _ => Subtype.ext C_add }

omit [Fintype σ] in
def projectiveToSpec : Proj (PolyGrade R σ) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom projectiveConstants)

omit [Fintype σ] in
@[reassoc]
lemma chart_toSpec (i : σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ≫ projectiveToSpec =
      Spec.map (CommRingCat.ofHom (chartConstants i)) := by
  rw [projectiveToSpec, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

omit [Fintype σ] in
                                                                            
lemma projective_affine_constants {Y : Scheme} (h : Y ⟶ Proj (PolyGrade R σ))
    (g : Y ⟶ Spec (CommRingCat.of R)) (hbase : h ≫ projectiveToSpec = g)
    (U : Y.affineOpens) [Algebra R Γ(Y, U.1)]
    (hOver : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U.1))) = U.2.fromSpec ≫ g)
    (i : σ) (φ : PolyChart (R := R) i →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) = U.2.fromSpec ≫ h) :
    ∀ c, φ (chartConstants i c) = algebraMap R Γ(Y, U.1) c := by
  have he : CommRingCat.ofHom (φ.comp (chartConstants i)) =
      CommRingCat.ofHom (algebraMap R Γ(Y, U.1)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← chart_toSpec,
      ← Category.assoc, hφ, Category.assoc, hbase, hOver]
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom he)

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveHyperplane {K : Type} [Field K] {n : ℕ} {X : Scheme}
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n)))) (t : Option (Fin n) → K) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (h ⁻¹ᵁ Proj.basicOpen (PolyGrade K (Option (Fin n))) (linearEquation t)).compl

theorem smooth_integral_hyperplane_of_etale_atlas
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
    (hbase : h ≫ projectiveToSpec = g)
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (φ : ∀ j, PolyChart (R := K) (e j none) →+* Γ(X, (U j).1))
    (hφ : ∀ j, Spec.map (CommRingCat.ofHom (φ j)) ≫
      Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X (e j none))
        (poly_X_mem (e j none)) (by decide) = (U j).2.fromSpec ≫ h)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j) (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₁ j)))) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₂ j)))) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (projectiveHyperplane h t).subscheme ∧
      Smooth ((projectiveHyperplane h t).subschemeι ≫ g) := by
  exact smooth_integral_zero_family X g U hcover hOver σ
    (fun j k => -φ j (chartCoordinate (e j none) (e j (some k))))
    i₁ i₂ a b hab hva hvb e
    (fun t => h ⁻¹ᵁ Proj.basicOpen (PolyGrade K (Option (Fin n))) (linearEquation t))
    (fun t j => hyperplane_affine_preimage_reindexed h (U j) (e j) (φ j) (hφ j)
      (projective_affine_constants h g hbase (U j) (hOver j) _ (φ j) (hφ j)) t)
    j₀ overlap hleft hright q hq

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
