import Mathlib

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeLineCharts
section
open CategoryTheory AlgebraicGeometry
open scoped Polynomial
universe u
variable (R : Type u) [CommRing R]

 
abbrev CoordinateRing := MvPolynomial (Fin 2) R
abbrev grading : ℕ → Submodule R (CoordinateRing R) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R

attribute [local instance] MvPolynomial.gradedAlgebra

def scheme : Scheme := AlgebraicGeometry.Proj (grading R)

abbrev x₀ : (CoordinateRing R) := MvPolynomial.X 0
abbrev x₁ : (CoordinateRing R) := MvPolynomial.X 1

lemma x₀_mem : (x₀ R) ∈ (grading R) 1 := MvPolynomial.isHomogeneous_X R 0
lemma x₁_mem : (x₁ R) ∈ (grading R) 1 := MvPolynomial.isHomogeneous_X R 1

 
abbrev ChartRing := HomogeneousLocalization.Away (grading R) (x₀ R)
abbrev FullChartRing := Localization.Away (x₀ R)

def constants : R →+* (grading R) 0 where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C (Fin 2) c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

instance chartAlgebra : Algebra R (ChartRing R) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading R) _).comp (constants R)).toAlgebra

 
def coordinate : (ChartRing R) :=
  HomogeneousLocalization.Away.mk (grading R) (x₀_mem R) 1 (x₁ R) (by simpa using (x₁_mem R))

 
def fromPoly : R[X] →ₐ[R] (ChartRing R) := Polynomial.aeval (coordinate R)

def dehom : (CoordinateRing R) →+* R[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then 1 else Polynomial.X)

@[simp] lemma dehom_x₀ : (dehom R) (x₀ R) = 1 := by simp [dehom, x₀]
@[simp] lemma dehom_x₁ : (dehom R) (x₁ R) = Polynomial.X := by simp [dehom, x₁]
@[simp] lemma dehom_C (a : R) : (dehom R) (MvPolynomial.C a) = Polynomial.C a := by
  simp [dehom]

def fullDehom : (FullChartRing R) →+* R[X] :=
  IsLocalization.Away.lift (x₀ R) (by rw [(dehom_x₀ R)]; exact isUnit_one)

def toPoly : (ChartRing R) →+* R[X] :=
  (fullDehom R).comp (algebraMap (ChartRing R) (FullChartRing R))

lemma toPoly_mk (n : ℕ) (p : (CoordinateRing R)) (hp : p ∈ (grading R) (n • 1)) :
    (toPoly R) (HomogeneousLocalization.Away.mk (grading R) (x₀_mem R) n p hp) = (dehom R) p := by
  change (fullDehom R) (Localization.mk p ⟨(x₀ R) ^ n, by use n⟩) = (dehom R) p
  rw [Localization.mk_eq_mk']
  apply (IsLocalization.lift_mk'_spec _ _ _ _).2
  simp

@[simp] lemma toPoly_algebraMap (a : R) :
    (toPoly R) (algebraMap R (ChartRing R) a) = Polynomial.C a := by
  change (toPoly R) (HomogeneousLocalization.Away.mk (grading R) (x₀_mem R) 0
    (MvPolynomial.C a) _) = _
  exact ((toPoly_mk R) 0 (MvPolynomial.C a) (by simp)).trans ((dehom_C R) a)

@[simp] lemma toPoly_coordinate : (toPoly R) (coordinate R) = Polynomial.X := by
  rw [coordinate, (toPoly_mk R), (dehom_x₁ R)]

def toPolyAlg : (ChartRing R) →ₐ[R] R[X] where
  __ := (toPoly R)
  commutes' := (toPoly_algebraMap R)

lemma toPoly_fromPoly (p : R[X]) : (toPoly R) ((fromPoly R) p) = p := by
  have h : (toPolyAlg R).comp (fromPoly R) = AlgHom.id R R[X] := by
    apply Polynomial.algHom_ext
    simp [fromPoly, toPolyAlg]
  exact DFunLike.congr_fun h p

lemma zero_degree_constant (c : (grading R) 0) :
    ∃ a : R, (constants R) a = c := by
  have h := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr c.property
  refine ⟨c.val.coeff 0, ?_⟩
  apply Subtype.ext
  exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm

lemma coordinate_power (a b : ℕ) :
    HomogeneousLocalization.Away.mk (grading R) (x₀_mem R) (a + b) ((x₀ R) ^ a * (x₁ R) ^ b)
      (by simpa using (SetLike.mul_mem_graded (SetLike.pow_mem_graded a (x₀_mem R))
        (SetLike.pow_mem_graded b (x₁_mem R)))) = (coordinate R) ^ b := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_pow,
    coordinate]
  simp only [Localization.mk_pow]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_iff_exists.mpr
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, SubmonoidClass.coe_pow, pow_one, pow_add]
  ring

lemma variables_generate :
    Algebra.adjoin ((grading R) 0) (Set.range (MvPolynomial.X : Fin 2 → (CoordinateRing R))) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C c => exact (Algebra.adjoin ((grading R) 0) _).algebraMap_mem ((constants R) c)
  | add p q hp hq => exact (Algebra.adjoin ((grading R) 0) _).add_mem hp hq
  | mul_X p i hp =>
    exact (Algebra.adjoin ((grading R) 0) _).mul_mem hp
      (Algebra.subset_adjoin (Set.mem_range_self i))

def polynomialRange : Subalgebra ((grading R) 0) (ChartRing R) where
  __ := (fromPoly R).range.toSubsemiring
  algebraMap_mem' c := by
    obtain ⟨a, rfl⟩ := (zero_degree_constant R) c
    exact ⟨Polynomial.C a, by simp [fromPoly]; rfl⟩

lemma fromPoly_surjective : Function.Surjective (fromPoly R) := by
  have htop := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top (x₀_mem R)
    (MvPolynomial.X : Fin 2 → (CoordinateRing R)) (variables_generate R) (fun _ => 1)
      (fun i => MvPolynomial.isHomogeneous_X R i)
  have hle : (⊤ : Submodule ((grading R) 0) (ChartRing R)) ≤ (polynomialRange R).toSubmodule := by
    rw [← htop, Submodule.span_le]
    rintro _ ⟨a, ai, hai, rfl⟩
    have he : a = ai 0 + ai 1 := by simpa [Fin.sum_univ_two] using hai.symm
    subst a
    have hm : (∏ i : Fin 2, (MvPolynomial.X i : (CoordinateRing R)) ^ ai i) =
        (x₀ R) ^ ai 0 * (x₁ R) ^ ai 1 := by simp [Fin.prod_univ_two]
    simp only [hm]
    rw [(coordinate_power R)]
    exact ⟨Polynomial.X ^ ai 1, by simp [fromPoly]⟩
  intro x
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule ((grading R) 0) (ChartRing R)))

 
theorem chart_polynomial_equiv :
    ∃ e : (ChartRing R) ≃+* R[X],
      (∀ a : R, e (algebraMap R (ChartRing R) a) = Polynomial.C a) ∧
      e (coordinate R) = Polynomial.X := by
  have hi : Function.Injective (toPoly R) := by
    intro x y h
    obtain ⟨p, rfl⟩ := (fromPoly_surjective R) x
    obtain ⟨q, rfl⟩ := (fromPoly_surjective R) y
    have hpq : p = q := by simpa only [(toPoly_fromPoly R)] using h
    exact congrArg (fromPoly R) hpq
  have hs : Function.Surjective (toPoly R) := fun p => ⟨(fromPoly R) p, (toPoly_fromPoly R) p⟩
  exact ⟨RingEquiv.ofBijective (toPoly R) ⟨hi, hs⟩, (toPoly_algebraMap R), (toPoly_coordinate R)⟩

end

section
open AlgebraicGeometry CategoryTheory
open scoped Polynomial
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
def chartEquiv : (ChartRing R) ≃+* R[X] := Classical.choose (chart_polynomial_equiv R)

lemma chartEquiv_constant (a : R) :
    (chartEquiv R) (algebraMap R (ChartRing R) a) = Polynomial.C a :=
  (Classical.choose_spec (chart_polynomial_equiv R)).1 a

lemma chartEquiv_coordinate : (chartEquiv R) (coordinate R) = Polynomial.X :=
  (Classical.choose_spec (chart_polynomial_equiv R)).2

lemma chartEquiv_fromPoly (p : R[X]) : (chartEquiv R) ((fromPoly R) p) = p := by
  have h : (chartEquiv R).toRingHom.comp (fromPoly R).toRingHom = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [fromPoly] using (chartEquiv_constant R) a
    · simpa [fromPoly] using (chartEquiv_coordinate R)
  exact DFunLike.congr_fun h p

abbrev RightChartRing := HomogeneousLocalization.Away (grading R) (x₁ R)

def rightCoordinate : (RightChartRing R) :=
  HomogeneousLocalization.Away.mk (grading R) (x₁_mem R) 1 (x₀ R) (by simpa using (x₀_mem R))

def swapVariables : (grading R) →+*ᵍ (grading R) where
  __ := (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)).toRingHom
  map_mem h := MvPolynomial.IsHomogeneous.rename_isHomogeneous h

@[simp] lemma swapVariables_x₀ : (swapVariables R) (x₀ R) = (x₁ R) := by
  simp [swapVariables, x₀, x₁]
@[simp] lemma swapVariables_x₁ : (swapVariables R) (x₁ R) = (x₀ R) := by
  simp [swapVariables, x₀, x₁]
@[simp] lemma swapVariables_C (a : R) :
    (swapVariables R) (MvPolynomial.C a) = MvPolynomial.C a := by simp [swapVariables]

lemma swapVariables_comp : (swapVariables R).comp (swapVariables R) = GradedRingHom.id (grading R) := by
  apply GradedRingHom.ext
  intro p
  change MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) p) = p
  rw [MvPolynomial.rename_rename]
  have h : ((Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2) ∘ Equiv.swap 0 1) = id := by
    funext i
    simp
  rw [h, MvPolynomial.rename_id_apply]

def leftToRight : (ChartRing R) →+* (RightChartRing R) :=
  HomogeneousLocalization.map (swapVariables R) (by
    rintro _ ⟨n, rfl⟩
    change (swapVariables R) ((x₀ R) ^ n) ∈ Submonoid.powers (x₁ R)
    simpa using (Submonoid.pow_mem (Submonoid.powers (x₁ R)) (Submonoid.mem_powers (x₁ R)) n))

def rightToLeft : (RightChartRing R) →+* (ChartRing R) :=
  HomogeneousLocalization.map (swapVariables R) (by
    rintro _ ⟨n, rfl⟩
    change (swapVariables R) ((x₁ R) ^ n) ∈ Submonoid.powers (x₀ R)
    simpa using (Submonoid.pow_mem (Submonoid.powers (x₀ R)) (Submonoid.mem_powers (x₀ R)) n))

lemma rightToLeft_leftToRight (x : (ChartRing R)) : (rightToLeft R) ((leftToRight R) x) = x := by
  change HomogeneousLocalization.map (swapVariables R) _ (HomogeneousLocalization.map (swapVariables R) _ x) = x
  simp only [HomogeneousLocalization.map_map, (swapVariables_comp R),
    HomogeneousLocalization.map_id, RingHom.id_apply]

lemma leftToRight_rightToLeft (x : (RightChartRing R)) : (leftToRight R) ((rightToLeft R) x) = x := by
  change HomogeneousLocalization.map (swapVariables R) _ (HomogeneousLocalization.map (swapVariables R) _ x) = x
  simp only [HomogeneousLocalization.map_map, (swapVariables_comp R),
    HomogeneousLocalization.map_id, RingHom.id_apply]

def chartSwap : (ChartRing R) ≃+* (RightChartRing R) where
  __ := (leftToRight R)
  invFun := (rightToLeft R)
  left_inv := (rightToLeft_leftToRight R)
  right_inv := (leftToRight_rightToLeft R)

lemma chartSwap_coordinate : (chartSwap R) (coordinate R) = (rightCoordinate R) := by
  simp [chartSwap, leftToRight, coordinate, rightCoordinate, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, (swapVariables_x₀ R), (swapVariables_x₁ R)]

lemma chartSwap_constant (a : R) :
    (chartSwap R) (algebraMap R (ChartRing R) a) =
      HomogeneousLocalization.fromZeroRingHom (grading R) _ ((constants R) a) := by
  change (chartSwap R) (HomogeneousLocalization.Away.mk (grading R) (x₀_mem R) 0
    (MvPolynomial.C a) _) = HomogeneousLocalization.Away.mk (grading R) (x₁_mem R) 0
    (MvPolynomial.C a) _
  simp [chartSwap, leftToRight, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, (swapVariables_C R)]

def rightChartEquiv : (RightChartRing R) ≃+* R[X] := (chartSwap R).symm.trans (chartEquiv R)

lemma rightChartEquiv_coordinate : (rightChartEquiv R) (rightCoordinate R) = Polynomial.X := by
  rw [← (chartSwap_coordinate R)]
  change (chartEquiv R) ((chartSwap R).symm ((chartSwap R) (coordinate R))) = _
  rw [RingEquiv.symm_apply_apply, (chartEquiv_coordinate R)]

end

open AlgebraicGeometry CategoryTheory Opposite
open scoped Polynomial LaurentPolynomial
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
def leftOpen : (scheme R).Opens := Proj.basicOpen (grading R) (x₀ R)
def rightOpen : (scheme R).Opens := Proj.basicOpen (grading R) (x₁ R)
abbrev OverlapRing := HomogeneousLocalization.Away (grading R) ((x₀ R) * (x₁ R))

def leftRestrict : (ChartRing R) →+* (OverlapRing R) :=
  HomogeneousLocalization.awayMap (grading R) (x₁_mem R) rfl

 
theorem standard_cover : (leftOpen R) ⊔ (rightOpen R) = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top' (grading R)
    (MvPolynomial.X : Fin 2 → (CoordinateRing R))
    (fun i => ⟨1, MvPolynomial.isHomogeneous_X R i⟩) (variables_generate R)
  apply top_unique
  erw [← h]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

instance overlapAlgebra : Algebra (ChartRing R) (OverlapRing R) := (leftRestrict R).toAlgebra

instance overlapLocalization : IsLocalization.Away (coordinate R) (OverlapRing R) := by
  convert (HomogeneousLocalization.Away.isLocalization_mul (x₀_mem R) (x₁_mem R) rfl
    (by decide : 1 ≠ 0)) using 1 <;>
    simp [coordinate, HomogeneousLocalization.Away.isLocalizationElem, overlapAlgebra, leftRestrict]

def overlapEquiv : (OverlapRing R) ≃+* R[T;T⁻¹] :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (coordinate R))
    (T := Submonoid.powers (Polynomial.X : R[X])) _ _ (chartEquiv R)
      (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers (chartEquiv_coordinate R))

lemma overlapEquiv_restrict (x : (ChartRing R)) :
    (overlapEquiv R) ((leftRestrict R) x) = ((chartEquiv R) x).toLaurent := by
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x

 

theorem overlap_laurent_equiv :
    ∃ e : (OverlapRing R) ≃+* R[T;T⁻¹],
      ∀ p : R[X], e ((leftRestrict R) ((fromPoly R) p)) = p.toLaurent := by
  exact ⟨(overlapEquiv R), fun p => by rw [(overlapEquiv_restrict R), (chartEquiv_fromPoly R)]⟩

def rightRestrict : (RightChartRing R) →+* (OverlapRing R) :=
  HomogeneousLocalization.awayMap (grading R) (x₀_mem R) (mul_comm (x₀ R) (x₁ R))

lemma restrict_coordinates_inverse : (leftRestrict R) (coordinate R) * (rightRestrict R) (rightCoordinate R) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [leftRestrict, rightRestrict, coordinate, rightCoordinate,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  rw [show (x₁ R) * (x₁ R) * ((x₀ R) * (x₀ R)) = (x₀ R) * (x₁ R) * ((x₀ R) * (x₁ R)) by ring, Localization.mk_eq_mk']
  exact IsLocalization.mk'_self (S := Localization.Away ((x₀ R) * (x₁ R))) _

lemma overlapEquiv_rightCoordinate :
    (overlapEquiv R) ((rightRestrict R) (rightCoordinate R)) = LaurentPolynomial.T (-1) := by
  have h := congrArg (overlapEquiv R) (restrict_coordinates_inverse R)
  rw [map_mul, map_one, (overlapEquiv_restrict R), (chartEquiv_coordinate R),
    Polynomial.toLaurent_X] at h
  calc
    (overlapEquiv R) ((rightRestrict R) (rightCoordinate R)) =
        LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 *
          (overlapEquiv R) ((rightRestrict R) (rightCoordinate R))) := by
      simp [← mul_assoc]
    _ = LaurentPolynomial.T (-1) := by rw [h, mul_one]

lemma restrict_constants (a : R) :
    (rightRestrict R) ((chartSwap R) (algebraMap R (ChartRing R) a)) =
      (leftRestrict R) (algebraMap R (ChartRing R) a) := by
  rw [(chartSwap_constant R)]
  change HomogeneousLocalization.awayMap (grading R) (x₀_mem R) (mul_comm (x₀ R) (x₁ R))
    (HomogeneousLocalization.fromZeroRingHom (grading R) _ ((constants R) a)) =
    HomogeneousLocalization.awayMap (grading R) (x₁_mem R) rfl
    (HomogeneousLocalization.fromZeroRingHom (grading R) _ ((constants R) a))
  rw [HomogeneousLocalization.awayMap_fromZeroRingHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom]

lemma overlapEquiv_right_fromPoly (p : R[X]) :
    (overlapEquiv R) ((rightRestrict R) ((chartSwap R) ((fromPoly R) p))) =
      LaurentPolynomial.invert p.toLaurent := by
  have h : (overlapEquiv R).toRingHom.comp ((rightRestrict R).comp
      ((chartSwap R).toRingHom.comp (fromPoly R).toRingHom)) =
      LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro a
      change (overlapEquiv R) ((rightRestrict R) ((chartSwap R) ((fromPoly R) (Polynomial.C a)))) = _
      rw [show (fromPoly R) (Polynomial.C a) = algebraMap R (ChartRing R) a by simp [fromPoly],
        (restrict_constants R), (overlapEquiv_restrict R), (chartEquiv_constant R)]
      simp
    · change (overlapEquiv R) ((rightRestrict R) ((chartSwap R) ((fromPoly R) Polynomial.X))) = _
      rw [show (fromPoly R) Polynomial.X = (coordinate R) by simp [fromPoly],
        (chartSwap_coordinate R), (overlapEquiv_rightCoordinate R)]
      simp
  exact DFunLike.congr_fun h p

lemma overlapEquiv_rightRestrict (x : (RightChartRing R)) :
    (overlapEquiv R) ((rightRestrict R) x) =
      LaurentPolynomial.invert ((rightChartEquiv R) x).toLaurent := by
  obtain ⟨y, rfl⟩ := (chartSwap R).surjective x
  obtain ⟨p, rfl⟩ := (fromPoly_surjective R) y
  rw [(overlapEquiv_right_fromPoly R)]
  change _ = LaurentPolynomial.invert ((chartEquiv R) ((chartSwap R).symm ((chartSwap R) ((fromPoly R) p)))).toLaurent
  rw [(chartSwap R).symm_apply_apply, (chartEquiv_fromPoly R)]

 
theorem right_chart_laurent_equiv :
    ∃ e : (RightChartRing R) ≃+* R[X], e (rightCoordinate R) = Polynomial.X ∧
      ∀ x, (overlapEquiv R) ((rightRestrict R) x) = LaurentPolynomial.invert (e x).toLaurent :=
  ⟨(rightChartEquiv R), (rightChartEquiv_coordinate R), (overlapEquiv_rightRestrict R)⟩

lemma overlap_eq_basic : (leftOpen R) ⊓ (rightOpen R) = Proj.basicOpen (grading R) ((x₀ R) * (x₁ R)) :=
  (Proj.basicOpen_mul (grading R) (x₀ R) (x₁ R)).symm

def leftSectionsIso : CommRingCat.of (ChartRing R) ≅ Γ((scheme R), (leftOpen R)) :=
  Proj.basicOpenIsoAway (grading R) (x₀ R) (x₀_mem R) (by decide)
def rightSectionsIso : CommRingCat.of (RightChartRing R) ≅ Γ((scheme R), (rightOpen R)) :=
  Proj.basicOpenIsoAway (grading R) (x₁ R) (x₁_mem R) (by decide)
def overlapSectionsIso : CommRingCat.of (OverlapRing R) ≅ Γ((scheme R), (leftOpen R) ⊓ (rightOpen R)) :=
  Proj.basicOpenIsoAway (grading R) ((x₀ R) * (x₁ R))
    (show (x₀ R) * (x₁ R) ∈ (grading R) (1 + 1) from SetLike.mul_mem_graded (x₀_mem R) (x₁_mem R)) (by decide) ≪≫
    (scheme R).presheaf.mapIso (eqToIso (overlap_eq_basic R)).op

def leftSectionEquiv : Γ((scheme R), (leftOpen R)) ≃+* R[X] :=
  (leftSectionsIso R).symm.commRingCatIsoToRingEquiv.trans (chartEquiv R)
def rightSectionEquiv : Γ((scheme R), (rightOpen R)) ≃+* R[X] :=
  (rightSectionsIso R).symm.commRingCatIsoToRingEquiv.trans (rightChartEquiv R)
def overlapSectionEquiv : Γ((scheme R), (leftOpen R) ⊓ (rightOpen R)) ≃+* R[T;T⁻¹] :=
  (overlapSectionsIso R).symm.commRingCatIsoToRingEquiv.trans (overlapEquiv R)

lemma leftSections_restrict :
    (leftSectionsIso R).hom ≫ (scheme R).presheaf.map (homOfLE inf_le_left).op =
      CommRingCat.ofHom (leftRestrict R) ≫ (overlapSectionsIso R).hom := by
  symm
  change CommRingCat.ofHom (leftRestrict R) ≫
    (Proj.awayToSection (grading R) ((x₀ R) * (x₁ R)) ≫ _) = _
  dsimp only [leftRestrict]
  rw [← Category.assoc, Proj.awayMap_awayToSection (grading R) (x₁_mem R) (rfl : (x₀ R) * (x₁ R) = (x₀ R) * (x₁ R))]
  change Proj.awayToSection (grading R) _ ≫
    (scheme R).presheaf.map _ ≫ (scheme R).presheaf.map _ = _
  erw [← (scheme R).presheaf.map_comp]
  rfl

lemma rightSections_restrict :
    (rightSectionsIso R).hom ≫ (scheme R).presheaf.map (homOfLE inf_le_right).op =
      CommRingCat.ofHom (rightRestrict R) ≫ (overlapSectionsIso R).hom := by
  symm
  change CommRingCat.ofHom (rightRestrict R) ≫
    (Proj.awayToSection (grading R) ((x₀ R) * (x₁ R)) ≫ _) = _
  dsimp only [rightRestrict]
  rw [← Category.assoc, Proj.awayMap_awayToSection (grading R) (x₀_mem R) (mul_comm (x₀ R) (x₁ R))]
  change Proj.awayToSection (grading R) _ ≫
    (scheme R).presheaf.map _ ≫ (scheme R).presheaf.map _ = _
  erw [← (scheme R).presheaf.map_comp]
  rfl

 

theorem standard_section_restrictions :
    (∀ s : Γ((scheme R), (leftOpen R)),
      (overlapSectionEquiv R) ((scheme R).presheaf.map (homOfLE inf_le_left).op s) =
        ((leftSectionEquiv R) s).toLaurent) ∧
    (∀ s : Γ((scheme R), (rightOpen R)),
      (overlapSectionEquiv R) ((scheme R).presheaf.map (homOfLE inf_le_right).op s) =
        LaurentPolynomial.invert ((rightSectionEquiv R) s).toLaurent) := by
  constructor
  · intro s
    obtain ⟨a, rfl⟩ := (leftSectionsIso R).commRingCatIsoToRingEquiv.surjective s
    have h := CategoryTheory.congr_fun (leftSections_restrict R) a
    change (scheme R).presheaf.map (homOfLE inf_le_left).op ((leftSectionsIso R).hom a) =
      (overlapSectionsIso R).hom ((leftRestrict R) a) at h
    change (overlapSectionEquiv R) ((scheme R).presheaf.map (homOfLE inf_le_left).op
      ((leftSectionsIso R).hom a)) = _
    rw [h]
    change (overlapEquiv R) ((overlapSectionsIso R).inv ((overlapSectionsIso R).hom ((leftRestrict R) a))) =
      ((chartEquiv R) ((leftSectionsIso R).inv ((leftSectionsIso R).hom a))).toLaurent
    simpa using (overlapEquiv_restrict R) a
  · intro s
    obtain ⟨a, rfl⟩ := (rightSectionsIso R).commRingCatIsoToRingEquiv.surjective s
    have h := CategoryTheory.congr_fun (rightSections_restrict R) a
    change (scheme R).presheaf.map (homOfLE inf_le_right).op ((rightSectionsIso R).hom a) =
      (overlapSectionsIso R).hom ((rightRestrict R) a) at h
    change (overlapSectionEquiv R) ((scheme R).presheaf.map (homOfLE inf_le_right).op
      ((rightSectionsIso R).hom a)) = _
    rw [h]
    change (overlapEquiv R) ((overlapSectionsIso R).inv ((overlapSectionsIso R).hom ((rightRestrict R) a))) =
      LaurentPolynomial.invert ((rightChartEquiv R) ((rightSectionsIso R).inv ((rightSectionsIso R).hom a))).toLaurent
    simpa using (overlapEquiv_rightRestrict R) a

end CampanaPeternellSix.RelativeLineCharts

end

end OAI
