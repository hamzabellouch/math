import OAI.AlgebraicGeometry.SurfaceCones.KummerShiftedOpen

namespace OAI

noncomputable section
open Algebra MvPolynomial
open nonZeroDivisors
namespace KummerShiftedDiagonal
open KummerLines
variable (p : ℕ) [Fact p.Prime]
instance : IsDomain C := inferInstanceAs (IsDomain (MvPolynomial (Fin 2) ℂ))
instance : Module.IsTorsionFree C (L p) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (chartMap_injective p)

/-- The actual open D((st+s+1)(s+1)(t+1)) of the blowup chart. -/
def T := Localization.Away chartDenominator
instance : CommRing T := inferInstanceAs (CommRing (Localization.Away chartDenominator))
instance : Algebra C T := OreLocalization.instAlgebra (R := C) (R₀ := C)
  (S := Submonoid.powers chartDenominator)
instance : IsLocalization.Away chartDenominator T := Localization.isLocalization
instance coordinateMappedLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (B p) (Submonoid.powers chartDenominator)) (S p) := by
  change IsLocalization ((Submonoid.powers chartDenominator).map (algebraMap C (B p))) (S p)
  rw [Submonoid.map_powers]
  exact inferInstanceAs (IsLocalization.Away (bDenominator p) (S p))
instance : Algebra T (S p) := localizationAlgebra (Submonoid.powers chartDenominator) (B p)
instance : IsScalarTower C T (S p) :=
  isScalarTower_localizationAlgebra (Submonoid.powers chartDenominator) (B p)
instance : Algebra T (L p) := ((algebraMap (S p) (L p)).comp (algebraMap T (S p))).toAlgebra
instance : IsScalarTower T (S p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := T) (S := S p) (A := L p) rfl
instance : IsScalarTower C T (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := C) (S := T) (A := L p) (by
  rw [IsScalarTower.algebraMap_eq C (S p) (L p), IsScalarTower.algebraMap_eq C T (S p)]
  rfl)
instance : Algebra.IsIntegral T (S p) := ⟨isIntegral_localization⟩
instance : Module.Finite T (S p) :=
  Module.Finite.of_isLocalizedModule (Submonoid.powers chartDenominator)
    (IsScalarTower.toAlgHom C (B p) (S p)).toLinearMap

instance : Algebra T (chartRootAlgebra p) :=
  ((algebraMap (S p) (chartRootAlgebra p)).comp (algebraMap T (S p))).toAlgebra
instance : IsScalarTower T (S p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' (R := T) (S := S p) (A := chartRootAlgebra p) rfl
instance : IsScalarTower T (chartRootAlgebra p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := T) (S := chartRootAlgebra p) (A := L p) (by
  rw [IsScalarTower.algebraMap_eq T (S p) (L p),
    IsScalarTower.algebraMap_eq (S p) (chartRootAlgebra p) (L p)]
  rfl)
instance : Algebra C (chartRootAlgebra p) :=
  ((algebraMap (S p) (chartRootAlgebra p)).comp (algebraMap C (S p))).toAlgebra
instance : IsScalarTower C (S p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' (R := C) (S := S p) (A := chartRootAlgebra p) rfl
instance : IsScalarTower C (chartRootAlgebra p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := C) (S := chartRootAlgebra p) (A := L p) (by
  rw [IsScalarTower.algebraMap_eq C (S p) (L p),
    IsScalarTower.algebraMap_eq (S p) (chartRootAlgebra p) (L p)]
  rfl)
instance : Module.Finite (S p) (chartRootAlgebra p) := (chartRootAlgebra_finiteFreeEtale p).2.1
instance : Module.Finite T (chartRootAlgebra p) := Module.Finite.trans (S p) (chartRootAlgebra p)
instance : IsIntegrallyClosed (chartRootAlgebra p) := (chartRootAlgebra_finiteFreeEtale p).2.2.2

lemma coordinateRoot_mem_chartRootAlgebra (i : Fin 2) :
    coordinateRoot p i ∈ chartRootAlgebra p := by
  have h := (chartRootAlgebra p).algebraMap_mem (algebraMap (B p) (S p) (bRoot p i))
  rw [← IsScalarTower.algebraMap_apply (B p) (S p) (L p)] at h
  exact h
lemma remainingRoot_mem_chartRootAlgebra (i : Fin 3) :
    remainingRoot p i ∈ chartRootAlgebra p := by
  apply Algebra.subset_adjoin
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
lemma allRoots_mem_chartRootAlgebra (i : Fin 5) :
    root p i ∈ chartRootAlgebra p := by
  fin_cases i
  · exact remainingRoot_mem_chartRootAlgebra p 0
  · exact remainingRoot_mem_chartRootAlgebra p 1
  · change root p 2 ∈ chartRootAlgebra p
    have he : root p 2 = coordinateRoot p 0 * remainingRoot p 2 := by
      change root p 2 = root p 3 * (root p 2 / root p 3)
      exact (mul_div_cancel₀ _ (root_ne_zero p 3)).symm
    rw [he]
    exact Subalgebra.mul_mem _ (coordinateRoot_mem_chartRootAlgebra p 0)
      (remainingRoot_mem_chartRootAlgebra p 2)
  · exact coordinateRoot_mem_chartRootAlgebra p 0
  · change root p 4 ∈ chartRootAlgebra p
    rw [original_root_four p]
    exact Subalgebra.mul_mem _ (coordinateRoot_mem_chartRootAlgebra p 0)
      (coordinateRoot_mem_chartRootAlgebra p 1)

/- The fraction field is the SAME original Kummer field, not a proper
subcover of it. The blowdown supplies the original plane action. -/
instance : Algebra R (S p) :=
  ((algebraMap C (S p)).comp (algebraMap R C)).toAlgebra
instance : IsScalarTower R C (S p) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := C) (A := S p) rfl
instance : IsScalarTower R (S p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := S p) (A := L p) (by
    rw [IsScalarTower.algebraMap_eq R C (L p), IsScalarTower.algebraMap_eq C (S p) (L p)]
    rfl)
instance : Algebra R (chartRootAlgebra p) :=
  ((algebraMap (S p) (chartRootAlgebra p)).comp (algebraMap R (S p))).toAlgebra
instance : IsScalarTower R (S p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := S p) (A := chartRootAlgebra p) rfl
instance : IsScalarTower R (chartRootAlgebra p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := chartRootAlgebra p) (A := L p) (by
    rw [IsScalarTower.algebraMap_eq R (S p) (L p),
      IsScalarTower.algebraMap_eq (S p) (chartRootAlgebra p) (L p)]
    rfl)
instance : IsFractionRing (chartRootAlgebra p) (L p) := by
  apply KummerEtale.fractionRing_of_generators ((chartRootAlgebra p).restrictScalars R)
    (Set.range (KummerCover.fieldRoot (p := p) radicand))
    (KummerCover.fieldRoot_generates radicand)
  rintro x ⟨i, rfl⟩
  exact allRoots_mem_chartRootAlgebra p i

/-- The entire normalization over this actual triple-point blowup open is the
regular algebra of the two ramified coordinates and three unit roots. -/
theorem chart_normalization : integralClosure T (L p) =
    (chartRootAlgebra p).restrictScalars T := by
  apply le_antisymm
  · intro x hx
    have hx' : IsIntegral (chartRootAlgebra p) x :=
      ((mem_integralClosure_iff T (L p)).mp hx).tower_top
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (L p)).mp
      (inferInstance : IsIntegrallyClosed (chartRootAlgebra p)) hx'
    change (a : L p) = x at ha
    exact ha ▸ a.property
  · intro x hx
    exact (mem_integralClosure_iff T (L p)).mpr
      ((Algebra.IsIntegral.isIntegral (R := T) (⟨x, hx⟩ : chartRootAlgebra p)).map
        (IsScalarTower.toAlgHom T (chartRootAlgebra p) (L p)))

/-- Regularity is asserted for the actual integral closure, not just a
subextension or the conditional diagonal coordinate algebra. -/
theorem chart_normalization_regular : IsRegularRing (integralClosure T (L p)) := by
  let : IsRegularRing ((chartRootAlgebra p).restrictScalars T) := chartRootAlgebra_regular p
  exact IsRegularRing.of_ringEquiv
    (Subalgebra.equivOfEq _ _ (chart_normalization p).symm).toRingEquiv
open scoped TensorProduct
/-- This normalization is the actual restriction of the normalization of
the blowup chart in the original five-root field. -/
def chartRestrictionEquiv :
    T ⊗[C] integralClosure C (L p) ≃ₐ[T] integralClosure T (L p) := by
  have : Algebra.Etale C T := Algebra.Etale.of_isLocalizationAway chartDenominator
  exact (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure C T (L p))
      TensorProduct.toIntegralClosure_bijective_of_smooth).trans
    (IsLocalization.algebraLid (Submonoid.powers chartDenominator) T (L p)).mapIntegralClosure

theorem normalization_chart_regular : IsRegularRing (T ⊗[C] integralClosure C (L p)) := by
  have : IsRegularRing (integralClosure T (L p)) := chart_normalization_regular p
  exact IsRegularRing.of_ringEquiv
    (R := integralClosure T (L p)) (chartRestrictionEquiv p).symm.toRingEquiv
end KummerShiftedDiagonal


end


noncomputable section
open Algebra MvPolynomial
namespace KummerShiftedDiagonal
open KummerLines
variable (p : ℕ) [Fact p.Prime]

lemma remainingRoot_inv_mem (i : Fin 3) : (remainingRoot p i)⁻¹ ∈ chartRootAlgebra p := by
  let z : chartRootAlgebra p := ⟨remainingRoot p i, remainingRoot_mem_chartRootAlgebra p i⟩
  have hz : z ^ p = algebraMap (S p) (chartRootAlgebra p)
      (algebraMap C (S p) (remainingForm i)) := by
    apply Subtype.ext
    exact (remainingRoot_pow p i).trans
      (IsScalarTower.algebraMap_apply C (S p) (L p) _)
  have hu : IsUnit (z ^ p) := by
    rw [hz]
    exact (remaining_unit p i).map (algebraMap (S p) (chartRootAlgebra p))
  exact Submonoid.inv_mem_of_isUnit ((isUnit_pow_iff (NeZero.ne p)).mp hu)
end KummerShiftedDiagonal

namespace ExplicitCone

def shiftedDiagonalSectionDenominator : sectionChart :=
  ⟨y 0 * y 1 * ratioQ, sectionChart.mul_mem
    (sectionChart.mul_mem (y_mem_sectionChart 0) (y_mem_sectionChart 1)) ratioQ_mem_sectionChart⟩
lemma shiftedDiagonalSectionDenominator_ne_zero : shiftedDiagonalSectionDenominator ≠ 0 := by
  intro h
  exact mul_ne_zero (mul_ne_zero (y_ne_zero 0) (y_ne_zero 1)) ratioQ_ne_zero
    (congrArg Subtype.val h)
def shiftedDiagonalSectionOpen : Subalgebra ℂ L :=
  FieldPrincipalOpen.away sectionChart shiftedDiagonalSectionDenominator shiftedDiagonalSectionDenominator_ne_zero

def shiftedDiagonalRegularAlgebra : Subalgebra ℂ L where
  toSubsemiring := (KummerShiftedDiagonal.chartRootAlgebra 7).toSubsemiring
  algebraMap_mem' c := by
    have h := (KummerShiftedDiagonal.chartRootAlgebra 7).algebraMap_mem
      (algebraMap (KummerShiftedDiagonal.B 7) (KummerShiftedDiagonal.S 7)
        (algebraMap ℂ (KummerShiftedDiagonal.B 7) c))
    rw [← IsScalarTower.algebraMap_apply (KummerShiftedDiagonal.B 7) (KummerShiftedDiagonal.S 7) L] at h
    exact h

lemma y_mem_shiftedDiagonalRegular (i : Fin 5) : y i ∈ shiftedDiagonalRegularAlgebra :=
  KummerShiftedDiagonal.allRoots_mem_chartRootAlgebra 7 i
lemma unitRoot_inv_mem_shiftedDiagonalRegular (i : Fin 3) :
    (KummerShiftedDiagonal.remainingRoot 7 i)⁻¹ ∈ shiftedDiagonalRegularAlgebra :=
  KummerShiftedDiagonal.remainingRoot_inv_mem 7 i

lemma ratioQ_mem_shiftedDiagonalRegular : ratioQ ∈ shiftedDiagonalRegularAlgebra := by
  have h0 : y 2 / y 3 ∈ shiftedDiagonalRegularAlgebra :=
    KummerShiftedDiagonal.remainingRoot_mem_chartRootAlgebra 7 2
  have h1 : (y 0)⁻¹ ∈ shiftedDiagonalRegularAlgebra := unitRoot_inv_mem_shiftedDiagonalRegular 0
  have he : ratioQ = (y 2 / y 3) * y 1 * (y 0)⁻¹ := by
    unfold ratioQ
    field_simp [y_ne_zero]
  rw [he]
  exact shiftedDiagonalRegularAlgebra.mul_mem
    (shiftedDiagonalRegularAlgebra.mul_mem h0 (y_mem_shiftedDiagonalRegular 1)) h1
lemma ratioR_mem_shiftedDiagonalRegular : ratioR ∈ shiftedDiagonalRegularAlgebra := by
  have h0 : y 4 / y 3 ∈ shiftedDiagonalRegularAlgebra :=
    KummerShiftedDiagonal.coordinateRoot_mem_chartRootAlgebra 7 1
  have h1 : (y 0)⁻¹ ∈ shiftedDiagonalRegularAlgebra := unitRoot_inv_mem_shiftedDiagonalRegular 0
  have he : ratioR = (y 4 / y 3) * (y 0)⁻¹ := by
    unfold ratioR
    field_simp [y_ne_zero]
  rw [he]
  exact shiftedDiagonalRegularAlgebra.mul_mem h0 h1
lemma sectionChart_le_shiftedDiagonalRegular : sectionChart ≤ shiftedDiagonalRegularAlgebra := by
  rw [sectionChart_eq]
  apply Algebra.adjoin_le
  rintro t (⟨i,rfl⟩ | ht)
  · exact y_mem_shiftedDiagonalRegular i
  · rcases (show t = ratioQ ∨ t = ratioR from by simpa using ht) with rfl | rfl
    · exact ratioQ_mem_shiftedDiagonalRegular
    · exact ratioR_mem_shiftedDiagonalRegular
lemma ratioQ_inv_mem_shiftedDiagonalRegular : ratioQ⁻¹ ∈ shiftedDiagonalRegularAlgebra := by
  have h0 : (y 2 / y 3)⁻¹ ∈ shiftedDiagonalRegularAlgebra := unitRoot_inv_mem_shiftedDiagonalRegular 2
  have h1 : (y 1)⁻¹ ∈ shiftedDiagonalRegularAlgebra := unitRoot_inv_mem_shiftedDiagonalRegular 1
  have he : ratioQ⁻¹ = (y 2 / y 3)⁻¹ * y 0 * (y 1)⁻¹ := by
    unfold ratioQ
    field_simp [y_ne_zero]
  rw [he]
  exact shiftedDiagonalRegularAlgebra.mul_mem
    (shiftedDiagonalRegularAlgebra.mul_mem h0 (y_mem_shiftedDiagonalRegular 0)) h1
lemma shiftedDiagonalSectionOpen_le : shiftedDiagonalSectionOpen ≤ shiftedDiagonalRegularAlgebra := by
  apply (FieldPrincipalOpen.away_le_iff sectionChart shiftedDiagonalSectionDenominator
    shiftedDiagonalSectionDenominator_ne_zero shiftedDiagonalRegularAlgebra).mpr
  refine ⟨sectionChart_le_shiftedDiagonalRegular, ?_⟩
  change (y 0 * y 1 * ratioQ)⁻¹ ∈ shiftedDiagonalRegularAlgebra
  rw [mul_inv_rev, mul_inv_rev]
  exact shiftedDiagonalRegularAlgebra.mul_mem ratioQ_inv_mem_shiftedDiagonalRegular
    (shiftedDiagonalRegularAlgebra.mul_mem (unitRoot_inv_mem_shiftedDiagonalRegular 1)
      (unitRoot_inv_mem_shiftedDiagonalRegular 0))

lemma sectionChart_le_shiftedDiagonalOpen : sectionChart ≤ shiftedDiagonalSectionOpen :=
  FieldPrincipalOpen.le_away sectionChart shiftedDiagonalSectionDenominator shiftedDiagonalSectionDenominator_ne_zero
lemma y_mem_shiftedDiagonalOpen (i : Fin 5) : y i ∈ shiftedDiagonalSectionOpen :=
  sectionChart_le_shiftedDiagonalOpen (y_mem_sectionChart i)
lemma ratioQ_mem_shiftedDiagonalOpen : ratioQ ∈ shiftedDiagonalSectionOpen :=
  sectionChart_le_shiftedDiagonalOpen ratioQ_mem_sectionChart
lemma ratioR_mem_shiftedDiagonalOpen : ratioR ∈ shiftedDiagonalSectionOpen :=
  sectionChart_le_shiftedDiagonalOpen ratioR_mem_sectionChart
lemma shiftedDiagonalProduct_inv_mem : (y 0 * y 1 * ratioQ)⁻¹ ∈ shiftedDiagonalSectionOpen :=
  FieldPrincipalOpen.inv_mem_away sectionChart shiftedDiagonalSectionDenominator shiftedDiagonalSectionDenominator_ne_zero
lemma y0_inv_mem_shiftedDiagonalOpen : (y 0)⁻¹ ∈ shiftedDiagonalSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem shiftedDiagonalSectionOpen
    (mul_ne_zero (y_ne_zero 1) ratioQ_ne_zero)
    (shiftedDiagonalSectionOpen.mul_mem (y_mem_shiftedDiagonalOpen 1) ratioQ_mem_shiftedDiagonalOpen)
  simpa only [mul_assoc] using shiftedDiagonalProduct_inv_mem
lemma y1_inv_mem_shiftedDiagonalOpen : (y 1)⁻¹ ∈ shiftedDiagonalSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem shiftedDiagonalSectionOpen
    (mul_ne_zero (y_ne_zero 0) ratioQ_ne_zero)
    (shiftedDiagonalSectionOpen.mul_mem (y_mem_shiftedDiagonalOpen 0) ratioQ_mem_shiftedDiagonalOpen)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using shiftedDiagonalProduct_inv_mem
lemma ratioQ_inv_mem_shiftedDiagonalOpen : ratioQ⁻¹ ∈ shiftedDiagonalSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem shiftedDiagonalSectionOpen
    (mul_ne_zero (y_ne_zero 0) (y_ne_zero 1))
    (shiftedDiagonalSectionOpen.mul_mem (y_mem_shiftedDiagonalOpen 0) (y_mem_shiftedDiagonalOpen 1))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using shiftedDiagonalProduct_inv_mem

lemma coordinateRoot_mem_shiftedDiagonalOpen (i : Fin 2) :
    KummerShiftedDiagonal.coordinateRoot 7 i ∈ shiftedDiagonalSectionOpen := by
  fin_cases i
  · exact y_mem_shiftedDiagonalOpen 3
  · change y 4 / y 3 ∈ shiftedDiagonalSectionOpen
    have he : y 4 / y 3 = ratioR * y 0 := by
      unfold ratioR
      field_simp [y_ne_zero]
    rw [he]
    exact shiftedDiagonalSectionOpen.mul_mem ratioR_mem_shiftedDiagonalOpen (y_mem_shiftedDiagonalOpen 0)
lemma B_mem_shiftedDiagonalOpen (b : KummerShiftedDiagonal.B 7) : (b : L) ∈ shiftedDiagonalSectionOpen := by
  have h := b.property
  change (b : L) ∈ Algebra.adjoin ℂ (Set.range (KummerShiftedDiagonal.coordinateRoot 7)) at h
  exact (Algebra.adjoin_le (by rintro _ ⟨i,rfl⟩; exact coordinateRoot_mem_shiftedDiagonalOpen i)) h
lemma remainingRoot_mem_shiftedDiagonalOpen (i : Fin 3) :
    KummerShiftedDiagonal.remainingRoot 7 i ∈ shiftedDiagonalSectionOpen := by
  fin_cases i
  · exact y_mem_shiftedDiagonalOpen 0
  · exact y_mem_shiftedDiagonalOpen 1
  · change y 2 / y 3 ∈ shiftedDiagonalSectionOpen
    have he : y 2 / y 3 = ratioQ * y 0 * (y 1)⁻¹ := by
      unfold ratioQ
      field_simp [y_ne_zero]
    rw [he]
    exact shiftedDiagonalSectionOpen.mul_mem
      (shiftedDiagonalSectionOpen.mul_mem ratioQ_mem_shiftedDiagonalOpen (y_mem_shiftedDiagonalOpen 0))
      y1_inv_mem_shiftedDiagonalOpen
lemma remainingRoot_inv_mem_shiftedDiagonalOpen (i : Fin 3) :
    (KummerShiftedDiagonal.remainingRoot 7 i)⁻¹ ∈ shiftedDiagonalSectionOpen := by
  fin_cases i
  · exact y0_inv_mem_shiftedDiagonalOpen
  · exact y1_inv_mem_shiftedDiagonalOpen
  · change (y 2 / y 3)⁻¹ ∈ shiftedDiagonalSectionOpen
    have he : (y 2 / y 3)⁻¹ = ratioQ⁻¹ * (y 0)⁻¹ * y 1 := by
      unfold ratioQ
      field_simp [y_ne_zero]
    rw [he]
    exact shiftedDiagonalSectionOpen.mul_mem
      (shiftedDiagonalSectionOpen.mul_mem ratioQ_inv_mem_shiftedDiagonalOpen y0_inv_mem_shiftedDiagonalOpen)
      (y_mem_shiftedDiagonalOpen 1)

lemma shiftedDiagonal_bDenominator_image :
    algebraMap (KummerShiftedDiagonal.B 7) L (KummerShiftedDiagonal.bDenominator 7) =
    KummerShiftedDiagonal.remainingRoot 7 0 ^ 7 * KummerShiftedDiagonal.remainingRoot 7 1 ^ 7 *
      KummerShiftedDiagonal.remainingRoot 7 2 ^ 7 := by
  change algebraMap (KummerShiftedDiagonal.B 7) L
    (algebraMap KummerShiftedDiagonal.C (KummerShiftedDiagonal.B 7) KummerShiftedDiagonal.chartDenominator) = _
  rw [← IsScalarTower.algebraMap_apply KummerShiftedDiagonal.C (KummerShiftedDiagonal.B 7) L]
  change algebraMap KummerShiftedDiagonal.C L
    (KummerShiftedDiagonal.remainingForm 0 * KummerShiftedDiagonal.remainingForm 1 * KummerShiftedDiagonal.remainingForm 2) = _
  simp only [map_mul, KummerShiftedDiagonal.remainingRoot_pow]
lemma bDenominator_inv_mem_shiftedDiagonalOpen :
    (algebraMap (KummerShiftedDiagonal.B 7) L (KummerShiftedDiagonal.bDenominator 7))⁻¹ ∈ shiftedDiagonalSectionOpen := by
  rw [shiftedDiagonal_bDenominator_image, mul_inv_rev, mul_inv_rev, ← inv_pow, ← inv_pow, ← inv_pow]
  exact shiftedDiagonalSectionOpen.mul_mem (shiftedDiagonalSectionOpen.pow_mem (remainingRoot_inv_mem_shiftedDiagonalOpen 2) 7)
    (shiftedDiagonalSectionOpen.mul_mem (shiftedDiagonalSectionOpen.pow_mem (remainingRoot_inv_mem_shiftedDiagonalOpen 1) 7)
      (shiftedDiagonalSectionOpen.pow_mem (remainingRoot_inv_mem_shiftedDiagonalOpen 0) 7))
lemma S_mem_shiftedDiagonalOpen (s : KummerShiftedDiagonal.S 7) :
    algebraMap (KummerShiftedDiagonal.S 7) L s ∈ shiftedDiagonalSectionOpen := by
  apply FieldPrincipalOpen.localizationImage_mem shiftedDiagonalSectionOpen (KummerShiftedDiagonal.bDenominator 7)
    ((isUnit_iff_ne_zero).mp (KummerShiftedDiagonal.bDenominator_unit_in_L 7))
    (fun b => B_mem_shiftedDiagonalOpen b) bDenominator_inv_mem_shiftedDiagonalOpen
lemma shiftedDiagonalRegular_le_sectionOpen : shiftedDiagonalRegularAlgebra ≤ shiftedDiagonalSectionOpen := by
  intro t ht
  change t ∈ Algebra.adjoin (KummerShiftedDiagonal.S 7) (KummerShiftedDiagonal.remainingRoots 7 : Set L) at ht
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    classical
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image _ from hx)
    exact remainingRoot_mem_shiftedDiagonalOpen i
  | algebraMap s => exact S_mem_shiftedDiagonalOpen s
  | add x y hx hy h₁ h₂ => exact shiftedDiagonalSectionOpen.add_mem h₁ h₂
  | mul x y hx hy h₁ h₂ => exact shiftedDiagonalSectionOpen.mul_mem h₁ h₂

/-- The literal polarization chart, localized at a*b*q, is exactly the
regular normalization of the literal shiftedDiagonal-point blowup open, within the
same original function field. -/
theorem shiftedDiagonalSectionOpen_eq : shiftedDiagonalSectionOpen = shiftedDiagonalRegularAlgebra :=
  le_antisymm shiftedDiagonalSectionOpen_le shiftedDiagonalRegular_le_sectionOpen

theorem sectionChart_shiftedDiagonalOpen_regular :
    IsRegularRing (Localization.Away shiftedDiagonalSectionDenominator) := by
  have : IsRegularRing shiftedDiagonalRegularAlgebra := KummerShiftedDiagonal.chartRootAlgebra_regular 7
  exact FieldPrincipalOpen.regular_away_of_eq sectionChart shiftedDiagonalSectionDenominator
    shiftedDiagonalSectionDenominator_ne_zero shiftedDiagonalRegularAlgebra shiftedDiagonalSectionOpen_eq

end ExplicitCone

end


noncomputable section
open Algebra MvPolynomial
namespace KummerNode
open KummerLines
variable (p : ℕ) [Fact p.Prime]
local instance : IsScalarTower ℂ R (L p) := IsScalarTower.of_algebraMap_eq' rfl
def coordinateRoot : Fin 2 → L p :=
  ![KummerCover.fieldRoot (p := p) radicand 0,
    KummerCover.fieldRoot (p := p) radicand 3]
def shiftedCoordinate : Fin 2 → R := ![X 0, X 1 - 1]
lemma shiftedCoordinate_independent : AlgebraicIndependent ℂ shiftedCoordinate := by
  apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions (algebraicIndependent_X (Fin 2) ℂ)
  intro i
  fin_cases i
  · exact Algebra.subset_adjoin ⟨0, rfl⟩
  · have hx : X (1 : Fin 2) - 1 ∈ Algebra.adjoin ℂ (Set.range shiftedCoordinate) :=
      Algebra.subset_adjoin ⟨1, rfl⟩
    simpa using (Algebra.adjoin ℂ (Set.range shiftedCoordinate)).add_mem hx
      (Subalgebra.one_mem _)
lemma coordinateRoot_pow (i : Fin 2) :
    coordinateRoot p i ^ p = algebraMap R (L p) (shiftedCoordinate i) := by
  fin_cases i
  · exact KummerCover.fieldRoot_pow (p := p) radicand 0
  · exact KummerCover.fieldRoot_pow (p := p) radicand 3

lemma coordinateRoot_independent : AlgebraicIndependent ℂ (coordinateRoot p) := by
  have hR : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  have h := shiftedCoordinate_independent.map (f := IsScalarTower.toAlgHom ℂ R (L p)) hR.injOn
  have he : (fun i => coordinateRoot p i ^ p) =
      (IsScalarTower.toAlgHom ℂ R (L p)) ∘ shiftedCoordinate := by
    funext i
    exact coordinateRoot_pow p i
  rw [← he] at h
  exact _root_.OAI.AlgebraicIndependent.of_powers (fun _ => p) h

/-- The ramified coordinate part of the literal cover at (x,y)=(0,1). -/
def coordinateAlgebra : Subalgebra ℂ (L p) :=
  Algebra.adjoin ℂ (Set.range (coordinateRoot p))
abbrev B := coordinateAlgebra p

def planeEquiv : R ≃ₐ[ℂ] B p := (coordinateRoot_independent p).aevalEquiv
instance : IsRegularRing (B p) :=
  IsRegularRing.of_ringEquiv (planeEquiv p).toRingEquiv
instance : IsIntegrallyClosed (B p) := by
  have hR : IsIntegrallyClosed R := UniqueFactorizationMonoid.instIsIntegrallyClosed
  exact IsIntegrallyClosed.of_equiv (R := R) (S := B p) (planeEquiv p).toRingEquiv

def bRoot (i : Fin 2) : B p :=
  ⟨coordinateRoot p i, Algebra.subset_adjoin (Set.mem_range_self i)⟩

/-- The original plane map sends x to u^p and y to v^p+1; its inclusion
in the original five-root field is exactly the source one. -/
def planeMap : R →ₐ[ℂ] B p := MvPolynomial.aeval ![bRoot p 0 ^ p, bRoot p 1 ^ p + 1]
lemma planeMap_comp : (coordinateAlgebra p).val.comp (planeMap p) =
    IsScalarTower.toAlgHom ℂ R (L p) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, planeMap, MvPolynomial.aeval_X]
  fin_cases i
  · change coordinateRoot p 0 ^ p = algebraMap R (L p) (X 0)
    exact coordinateRoot_pow p 0
  · change coordinateRoot p 1 ^ p + 1 = algebraMap R (L p) (X 1)
    have h := coordinateRoot_pow p 1
    change coordinateRoot p 1 ^ p = algebraMap R (L p) (X 1 - 1) at h
    rw [h, map_sub, map_one]
    ring
instance : Algebra R (B p) := (planeMap p).toRingHom.toAlgebra
instance : IsScalarTower ℂ R (B p) := IsScalarTower.of_algebraMap_eq'
  (AlgHom.comp_algebraMap (planeMap p)).symm
instance : IsScalarTower R (B p) (L p) := IsScalarTower.of_algebraMap_eq' (by
  exact congrArg AlgHom.toRingHom (planeMap_comp p).symm)

lemma root_integral (i : Fin 5) :
    IsIntegral R (KummerCover.fieldRoot (p := p) radicand i) := by
  refine ⟨Polynomial.X ^ p - Polynomial.C (lineForm i),
    Polynomial.monic_X_pow_sub_C _ (NeZero.ne p), ?_⟩
  change Polynomial.aeval (KummerCover.fieldRoot (p := p) radicand i)
    (Polynomial.X ^ p - Polynomial.C (lineForm i)) = 0
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  exact sub_eq_zero.mpr (KummerCover.fieldRoot_pow radicand i)

instance : Algebra.IsIntegral R (B p) := by
  have hB : coordinateAlgebra p ≤ (integralClosure R (L p)).restrictScalars ℂ := by
    apply Algebra.adjoin_le
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact root_integral p 0
    · exact root_integral p 3
  constructor
  intro b
  have hi : IsIntegral R (b : L p) := hB b.property
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R (B p) (L p))
    Subtype.val_injective).mp hi

instance : Algebra.FiniteType ℂ (B p) := by
  exact Algebra.FiniteType.of_surjective (planeEquiv p).toAlgHom (planeEquiv p).surjective
instance : Algebra.FiniteType R (B p) := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R (B p)
instance : Module.Finite R (B p) := Algebra.IsIntegral.finite
end KummerNode

end


noncomputable section
open Algebra MvPolynomial
namespace KummerAffineExtra
open KummerLines
variable (p : ℕ) [Fact p.Prime]
local instance : IsScalarTower ℂ R (L p) := IsScalarTower.of_algebraMap_eq' rfl

/-- The other ordinary affine node, and the open part of the diagonal.
Together with the node (0,1), these will cover the complement of the two
actual affine triple points. -/
def coordinateIndex : Fin 2 → Fin 2 → Fin 5 := ![![1, 2], ![0, 4]]
def coordinateRoot (j : Fin 2) (i : Fin 2) : L p :=
  KummerCover.fieldRoot (p := p) radicand (coordinateIndex j i)
def coordinateForm (j : Fin 2) (i : Fin 2) : R := lineForm (coordinateIndex j i)
lemma coordinateForm_independent (j : Fin 2) : AlgebraicIndependent ℂ (coordinateForm j) := by
  apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions (algebraicIndependent_X (Fin 2) ℂ)
  have h0 : coordinateForm j 0 ∈ Algebra.adjoin ℂ (Set.range (coordinateForm j)) :=
    Algebra.subset_adjoin (Set.mem_range_self 0)
  have h1 : coordinateForm j 1 ∈ Algebra.adjoin ℂ (Set.range (coordinateForm j)) :=
    Algebra.subset_adjoin (Set.mem_range_self 1)
  intro i
  fin_cases j <;> fin_cases i
  · change X (0 : Fin 2) ∈ _
    change X (0 : Fin 2) - 1 ∈ _ at h1
    simpa using (Algebra.adjoin ℂ (Set.range (coordinateForm 0))).add_mem h1
      (Subalgebra.one_mem _)
  · exact h0
  · exact h0
  · change X (1 : Fin 2) ∈ _
    change X (0 : Fin 2) ∈ _ at h0
    change X (0 : Fin 2) - X (1 : Fin 2) ∈ _ at h1
    simpa using (Algebra.adjoin ℂ (Set.range (coordinateForm 1))).sub_mem h0 h1
lemma coordinateRoot_pow (j i : Fin 2) :
    coordinateRoot p j i ^ p = algebraMap R (L p) (coordinateForm j i) :=
  KummerCover.fieldRoot_pow radicand (coordinateIndex j i)
lemma coordinateRoot_independent (j : Fin 2) : AlgebraicIndependent ℂ (coordinateRoot p j) := by
  have hR : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  have h := (coordinateForm_independent j).map
    (f := IsScalarTower.toAlgHom ℂ R (L p)) hR.injOn
  have he : (fun i => coordinateRoot p j i ^ p) =
      (IsScalarTower.toAlgHom ℂ R (L p)) ∘ coordinateForm j := by
    funext i
    exact coordinateRoot_pow p j i
  rw [← he] at h
  exact _root_.OAI.AlgebraicIndependent.of_powers (fun _ => p) h

def coordinateAlgebra (j : Fin 2) : Subalgebra ℂ (L p) :=
  Algebra.adjoin ℂ (Set.range (coordinateRoot p j))
abbrev B (j : Fin 2) := coordinateAlgebra p j
def planeEquiv (j : Fin 2) : R ≃ₐ[ℂ] B p j := (coordinateRoot_independent p j).aevalEquiv
instance (j : Fin 2) : IsRegularRing (B p j) :=
  IsRegularRing.of_ringEquiv (planeEquiv p j).toRingEquiv
instance (j : Fin 2) : IsIntegrallyClosed (B p j) := by
  have hR : IsIntegrallyClosed R := UniqueFactorizationMonoid.instIsIntegrallyClosed
  exact IsIntegrallyClosed.of_equiv (R := R) (S := B p j) (planeEquiv p j).toRingEquiv

def bRoot (j i : Fin 2) : B p j :=
  ⟨coordinateRoot p j i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
def planeMap (j : Fin 2) : R →ₐ[ℂ] B p j :=
  MvPolynomial.aeval (if j = 0 then ![bRoot p j 1 ^ p + 1, bRoot p j 0 ^ p]
    else ![bRoot p j 0 ^ p, bRoot p j 0 ^ p - bRoot p j 1 ^ p])
lemma planeMap_comp (j : Fin 2) : (coordinateAlgebra p j).val.comp (planeMap p j) =
    IsScalarTower.toAlgHom ℂ R (L p) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, planeMap, MvPolynomial.aeval_X]
  fin_cases j <;> fin_cases i
  · change coordinateRoot p 0 1 ^ p + 1 = algebraMap R (L p) (X 0)
    rw [coordinateRoot_pow]
    change algebraMap R (L p) (X 0 - 1) + 1 = _
    rw [map_sub, map_one]
    ring
  · change coordinateRoot p 0 0 ^ p = algebraMap R (L p) (X 1)
    exact coordinateRoot_pow p 0 0
  · change coordinateRoot p 1 0 ^ p = algebraMap R (L p) (X 0)
    exact coordinateRoot_pow p 1 0
  · change coordinateRoot p 1 0 ^ p - coordinateRoot p 1 1 ^ p =
      algebraMap R (L p) (X 1)
    rw [coordinateRoot_pow, coordinateRoot_pow]
    change algebraMap R (L p) (X 0) - algebraMap R (L p) (X 0 - X 1) = _
    rw [map_sub]
    ring
instance (j : Fin 2) : Algebra R (B p j) := (planeMap p j).toRingHom.toAlgebra
instance (j : Fin 2) : IsScalarTower ℂ R (B p j) := IsScalarTower.of_algebraMap_eq'
  (AlgHom.comp_algebraMap (planeMap p j)).symm
instance (j : Fin 2) : IsScalarTower R (B p j) (L p) := IsScalarTower.of_algebraMap_eq' (by
  exact congrArg AlgHom.toRingHom (planeMap_comp p j).symm)
instance (j : Fin 2) : Algebra.IsIntegral R (B p j) := by
  have hB : coordinateAlgebra p j ≤ (integralClosure R (L p)).restrictScalars ℂ := by
    apply Algebra.adjoin_le
    rintro z ⟨i, rfl⟩
    exact KummerNode.root_integral p (coordinateIndex j i)
  constructor
  intro b
  have hi : IsIntegral R (b : L p) := hB b.property
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R (B p j) (L p))
    Subtype.val_injective).mp hi
instance (j : Fin 2) : Algebra.FiniteType ℂ (B p j) :=
  Algebra.FiniteType.of_surjective (planeEquiv p j).toAlgHom (planeEquiv p j).surjective
instance (j : Fin 2) : Algebra.FiniteType R (B p j) :=
  Algebra.FiniteType.of_restrictScalars_finiteType ℂ R (B p j)
instance (j : Fin 2) : Module.Finite R (B p j) := Algebra.IsIntegral.finite
end KummerAffineExtra

end


noncomputable section
open Algebra MvPolynomial
open nonZeroDivisors
namespace KummerAffineExtra
open KummerLines
variable (p : ℕ) [Fact p.Prime] (j : Fin 2)
local instance : IsScalarTower ℂ R (L p) := IsScalarTower.of_algebraMap_eq' rfl

def remainingIndex : Fin 2 → Fin 3 → Fin 5 := ![![0, 3, 4], ![1, 2, 3]]
def chartDenominator : R :=
  lineForm (remainingIndex j 0) * lineForm (remainingIndex j 1) * lineForm (remainingIndex j 2)
lemma chartDenominator_ne_zero : chartDenominator j ≠ 0 :=
  mul_ne_zero (mul_ne_zero (prime_lineForm (remainingIndex j 0)).ne_zero
    (prime_lineForm (remainingIndex j 1)).ne_zero) (prime_lineForm (remainingIndex j 2)).ne_zero
lemma planeMap_injective : Function.Injective (planeMap p j) := by
  have hR : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  intro a b h
  apply hR
  exact congrArg (fun g : R →ₐ[ℂ] L p => g a) (planeMap_comp p j).symm |>.trans
    ((congrArg (fun z : B p j => (z : L p)) h).trans
      (congrArg (fun g : R →ₐ[ℂ] L p => g b) (planeMap_comp p j)))

def bDenominator : B p j := planeMap p j (chartDenominator j)
lemma bDenominator_ne_zero : bDenominator p j ≠ 0 :=
  (map_ne_zero_iff _ (planeMap_injective p j)).mpr (chartDenominator_ne_zero j)
lemma bPowers_le : Submonoid.powers (bDenominator p j) ≤ (B p j)⁰ := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n (bDenominator_ne_zero p j))

def S := Localization.Away (bDenominator p j)
instance : CommRing (S p j) := inferInstanceAs (CommRing (Localization.Away (bDenominator p j)))
instance : Algebra (B p j) (S p j) :=
  OreLocalization.instAlgebra (R := B p j) (R₀ := B p j)
    (S := Submonoid.powers (bDenominator p j))
instance : IsLocalization.Away (bDenominator p j) (S p j) := Localization.isLocalization
instance : IsDomain (S p j) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ (bPowers_le p j)
instance : IsIntegrallyClosed (S p j) :=
  isIntegrallyClosed_of_isLocalization (S p j) (Submonoid.powers (bDenominator p j)) (bPowers_le p j)
instance : Algebra.Etale (B p j) (S p j) :=
  Algebra.Etale.of_isLocalizationAway (bDenominator p j)
instance : IsRegularRing (S p j) := EtaleRegular.regular (B p j) (S p j)

lemma bDenominator_unit_in_L : IsUnit (algebraMap (B p j) (L p) (bDenominator p j)) := by
  apply isUnit_iff_ne_zero.mpr
  exact (map_ne_zero_iff _ (Subtype.val_injective)).mpr (bDenominator_ne_zero p j)

instance : Algebra (S p j) (L p) :=
  (IsLocalization.Away.lift (bDenominator p j) (bDenominator_unit_in_L p j) : S p j →+* L p).toAlgebra
instance : IsScalarTower (B p j) (S p j) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := B p j) (S := S p j) (A := L p)
    (IsLocalization.Away.lift_comp (S := S p j) (bDenominator p j) (bDenominator_unit_in_L p j)).symm
instance : Module.IsTorsionFree (S p j) (L p) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  change Function.Injective (IsLocalization.Away.lift (bDenominator p j) (bDenominator_unit_in_L p j))
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  rw [(IsLocalization.injective (S p j) (bPowers_le p j)).eq_iff]
  change a = b ↔ (a : L p) = (b : L p)
  exact Subtype.val_injective.eq_iff.symm
instance : Algebra R (S p j) := (algebraMap (B p j) (S p j)).comp (algebraMap R (B p j)) |>.toAlgebra
instance : IsScalarTower R (B p j) (S p j) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := B p j) (A := S p j) rfl
instance : IsScalarTower R (S p j) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := S p j) (A := L p) (by
  rw [IsScalarTower.algebraMap_eq R (B p j) (L p), IsScalarTower.algebraMap_eq (B p j) (S p j) (L p)]
  rfl)

lemma remaining_dvd (i : Fin 3) : lineForm (remainingIndex j i) ∣ chartDenominator j := by
  fin_cases i <;> simp only [chartDenominator, Fin.isValue]
  · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact dvd_mul_left _ _
lemma remaining_unit (i : Fin 3) : IsUnit (algebraMap R (S p j) (lineForm (remainingIndex j i))) :=
  IsLocalization.Away.isUnit_of_dvd (S := S p j) (bDenominator p j)
    (map_dvd (planeMap p j) (remaining_dvd j i))
lemma exponent_unit : IsUnit (p : S p j) := by
  have hC : IsUnit (p : ℂ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (NeZero.ne p))
  have hB : IsUnit (p : B p j) := by simpa using hC.map (algebraMap ℂ (B p j))
  simpa using hB.map (algebraMap (B p j) (S p j))

def remainingRoots : Finset (L p) := by
  classical
  exact Finset.univ.image (fun i : Fin 3 => KummerCover.fieldRoot (p := p) radicand (remainingIndex j i))
abbrev chartRootAlgebra := Algebra.adjoin (S p j) (remainingRoots p j : Set (L p))

theorem chartRootAlgebra_finiteFreeEtale :
    Algebra.Etale (S p j) (chartRootAlgebra p j) ∧
    Module.Finite (S p j) (chartRootAlgebra p j) ∧
    Module.Free (S p j) (chartRootAlgebra p j) ∧
    IsIntegrallyClosed (chartRootAlgebra p j) := by
  apply KummerEtale.finite_unit_roots p (NeZero.pos p) (exponent_unit p j)
  intro x hx
  classical
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image _ from hx)
  refine ⟨(remaining_unit p j i).unit, ?_⟩
  rw [IsUnit.unit_spec, ← IsScalarTower.algebraMap_apply R (S p j) (L p)]
  exact KummerCover.fieldRoot_pow radicand (remainingIndex j i)

theorem chartRootAlgebra_regular : IsRegularRing (chartRootAlgebra p j) := by
  have := (chartRootAlgebra_finiteFreeEtale p j).1
  exact EtaleRegular.regular (S p j) (chartRootAlgebra p j)
end KummerAffineExtra

end


noncomputable section
open Algebra MvPolynomial
open nonZeroDivisors
namespace KummerAffineExtra
open KummerLines
variable (p : ℕ) [Fact p.Prime] (j : Fin 2)

/-- The two other explicit affine opens of the original plane. -/
def T := Localization.Away (chartDenominator j)
instance : CommRing (T j) := inferInstanceAs (CommRing (Localization.Away (chartDenominator j)))
instance : Algebra R (T j) := OreLocalization.instAlgebra (R := R) (R₀ := R)
  (S := Submonoid.powers (chartDenominator j))
instance : IsLocalization.Away (chartDenominator j) (T j) := Localization.isLocalization
instance coordinateMappedLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (B p j) (Submonoid.powers (chartDenominator j))) (S p j) := by
  change IsLocalization ((Submonoid.powers (chartDenominator j)).map (algebraMap R (B p j))) (S p j)
  rw [Submonoid.map_powers]
  exact inferInstanceAs (IsLocalization.Away (bDenominator p j) (S p j))
instance : Algebra (T j) (S p j) := localizationAlgebra (Submonoid.powers (chartDenominator j)) (B p j)
instance : IsScalarTower R (T j) (S p j) :=
  isScalarTower_localizationAlgebra (Submonoid.powers (chartDenominator j)) (B p j)
instance : Algebra (T j) (L p) := ((algebraMap (S p j) (L p)).comp (algebraMap (T j) (S p j))).toAlgebra
instance : IsScalarTower (T j) (S p j) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := (T j)) (S := S p j) (A := L p) rfl
instance : IsScalarTower R (T j) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := (T j)) (A := L p) (by
  rw [IsScalarTower.algebraMap_eq R (S p j) (L p), IsScalarTower.algebraMap_eq R (T j) (S p j)]
  rfl)
instance : Algebra.IsIntegral (T j) (S p j) := ⟨isIntegral_localization⟩
instance : Module.Finite (T j) (S p j) :=
  Module.Finite.of_isLocalizedModule (Submonoid.powers (chartDenominator j))
    (IsScalarTower.toAlgHom R (B p j) (S p j)).toLinearMap

instance : Algebra (T j) (chartRootAlgebra p j) :=
  ((algebraMap (S p j) (chartRootAlgebra p j)).comp (algebraMap (T j) (S p j))).toAlgebra
instance : IsScalarTower (T j) (S p j) (chartRootAlgebra p j) :=
  IsScalarTower.of_algebraMap_eq' (R := (T j)) (S := S p j) (A := chartRootAlgebra p j) rfl
instance : IsScalarTower (T j) (chartRootAlgebra p j) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := (T j)) (S := chartRootAlgebra p j) (A := L p) (by
  rw [IsScalarTower.algebraMap_eq (T j) (S p j) (L p),
    IsScalarTower.algebraMap_eq (S p j) (chartRootAlgebra p j) (L p)]
  rfl)
instance : Algebra R (chartRootAlgebra p j) :=
  ((algebraMap (S p j) (chartRootAlgebra p j)).comp (algebraMap R (S p j))).toAlgebra
instance : IsScalarTower R (S p j) (chartRootAlgebra p j) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := S p j) (A := chartRootAlgebra p j) rfl
instance : IsScalarTower R (chartRootAlgebra p j) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := chartRootAlgebra p j) (A := L p) (by
  rw [IsScalarTower.algebraMap_eq R (S p j) (L p),
    IsScalarTower.algebraMap_eq (S p j) (chartRootAlgebra p j) (L p)]
  rfl)
instance : Module.Finite (S p j) (chartRootAlgebra p j) := (chartRootAlgebra_finiteFreeEtale p j).2.1
instance : Module.Finite (T j) (chartRootAlgebra p j) := Module.Finite.trans (S p j) (chartRootAlgebra p j)
instance : IsIntegrallyClosed (chartRootAlgebra p j) := (chartRootAlgebra_finiteFreeEtale p j).2.2.2

lemma coordinateRoot_mem_chartRootAlgebra (i : Fin 2) :
    coordinateRoot p j i ∈ chartRootAlgebra p j := by
  have h := (chartRootAlgebra p j).algebraMap_mem (algebraMap (B p j) (S p j) (bRoot p j i))
  rw [← IsScalarTower.algebraMap_apply (B p j) (S p j) (L p)] at h
  exact h
lemma remainingRoot_mem_chartRootAlgebra (i : Fin 3) :
    KummerCover.fieldRoot (p := p) radicand (remainingIndex j i) ∈ chartRootAlgebra p j := by
  apply Algebra.subset_adjoin
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
lemma allRoots_mem_chartRootAlgebra (i : Fin 5) :
    KummerCover.fieldRoot (p := p) radicand i ∈ chartRootAlgebra p j := by
  fin_cases j <;> fin_cases i
  · exact remainingRoot_mem_chartRootAlgebra p 0 0
  · exact coordinateRoot_mem_chartRootAlgebra p 0 0
  · exact coordinateRoot_mem_chartRootAlgebra p 0 1
  · exact remainingRoot_mem_chartRootAlgebra p 0 1
  · exact remainingRoot_mem_chartRootAlgebra p 0 2
  · exact coordinateRoot_mem_chartRootAlgebra p 1 0
  · exact remainingRoot_mem_chartRootAlgebra p 1 0
  · exact remainingRoot_mem_chartRootAlgebra p 1 1
  · exact remainingRoot_mem_chartRootAlgebra p 1 2
  · exact coordinateRoot_mem_chartRootAlgebra p 1 1

instance : IsFractionRing (chartRootAlgebra p j) (L p) := by
  apply KummerEtale.fractionRing_of_generators (K := K)
    ((chartRootAlgebra p j).restrictScalars R)
    (Set.range (KummerCover.fieldRoot (p := p) radicand))
    (KummerCover.fieldRoot_generates radicand)
  rintro x ⟨i, rfl⟩
  exact allRoots_mem_chartRootAlgebra p j i

/-- The entire normalization over this actual affine chart open is the
regular algebra of the two ramified coordinates and three unit roots. -/
theorem chart_normalization : integralClosure (T j) (L p) =
    (chartRootAlgebra p j).restrictScalars (T j) := by
  apply le_antisymm
  · intro x hx
    have hx' : IsIntegral (chartRootAlgebra p j) x :=
      ((mem_integralClosure_iff (T j) (L p)).mp hx).tower_top
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (L p)).mp
      (inferInstance : IsIntegrallyClosed (chartRootAlgebra p j)) hx'
    change (a : L p) = x at ha
    exact ha ▸ a.property
  · intro x hx
    exact (mem_integralClosure_iff (T j) (L p)).mpr
      ((Algebra.IsIntegral.isIntegral (R := (T j)) (⟨x, hx⟩ : chartRootAlgebra p j)).map
        (IsScalarTower.toAlgHom (T j) (chartRootAlgebra p j) (L p)))

/-- Regularity is asserted for the actual integral closure, not just a
subextension or the conditional diagonal coordinate algebra. -/
theorem chart_normalization_regular : IsRegularRing (integralClosure (T j) (L p)) := by
  let : IsRegularRing ((chartRootAlgebra p j).restrictScalars (T j)) := chartRootAlgebra_regular p j
  exact IsRegularRing.of_ringEquiv
    (Subalgebra.equivOfEq _ _ (chart_normalization p j).symm).toRingEquiv
open scoped TensorProduct
/-- This same normalization is the actual restriction of the original
normalized five-root affine cover, not a newly chosen function field. -/
def chartRestrictionEquiv :
    (T j) ⊗[R] integralClosure R (L p) ≃ₐ[(T j)] integralClosure (T j) (L p) := by
  have : Algebra.Etale R (T j) := Algebra.Etale.of_isLocalizationAway (chartDenominator j)
  exact (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R (T j) (L p))
      TensorProduct.toIntegralClosure_bijective_of_smooth).trans
    (IsLocalization.algebraLid (Submonoid.powers (chartDenominator j)) (T j) (L p)).mapIntegralClosure

theorem normalization_chart_regular : IsRegularRing ((T j) ⊗[R] integralClosure R (L p)) := by
  have : IsRegularRing (integralClosure (T j) (L p)) := chart_normalization_regular p j
  exact IsRegularRing.of_ringEquiv
    (R := integralClosure (T j) (L p)) (chartRestrictionEquiv p j).symm.toRingEquiv
end KummerAffineExtra


end


noncomputable section
namespace RegularLocalization
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- Regularity is preserved under an arbitrary localization, proved by
identifying every prime local ring rather than asserting smoothness. -/
theorem regular (M : Submonoid A) [IsLocalization M S] [IsRegularRing A] :
    IsRegularRing S := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  apply isRegularRing_iff.mpr
  intro q hq
  let p := q.comap (algebraMap A S)
  have : p.IsPrime := Ideal.IsPrime.comap (algebraMap A S)
  have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q)).toRingEquiv
end RegularLocalization

end

end OAI
