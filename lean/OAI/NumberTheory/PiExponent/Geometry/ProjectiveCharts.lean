import Mathlib

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
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

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

def chartSectionRingEquiv :
    Γ(Proj (PolyGrade R σ), Proj.basicOpen (PolyGrade R σ) (X i)) ≃+*
      MvPolynomial (ChartVariables i) R :=
  ((Proj.basicOpen (PolyGrade R σ) (X i)).topIso.symm ≪≫
    Scheme.Γ.mapIso (projectiveChartIso (R := R) i).symm.op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ChartVariables i) R))).commRingCatIsoToRingEquiv

lemma standardChart_isAffineOpen :
    IsAffineOpen (Proj.basicOpen (PolyGrade R σ) (X i)) :=
  Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide)

lemma standardChart_cover :
    (⨆ i : σ, Proj.basicOpen (PolyGrade R σ) (X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ R
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

end PiExponentSeshadri.Projective

end

end OAI
