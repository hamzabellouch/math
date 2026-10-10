import OAI.AlgebraicGeometry.SurfaceCones.KummerUnramifiedNormalization

namespace OAI

noncomputable section
open Algebra MvPolynomial
open nonZeroDivisors
namespace KummerTriple
open KummerLines
variable (p : ℕ) [Fact p.Prime]

/-- The actual blowup chart open containing s=t=0 (the intersection of
its exceptional divisor with the strict transform of y=0). -/
def cX (i : Fin 2) : C := X i
def chartDenominator : C := (cX 0 - 1) * (cX 0 * cX 1 - 1) * (1 - cX 1)
lemma chartDenominator_ne_zero : chartDenominator ≠ 0 := by
  let f : C →+* ℂ := MvPolynomial.eval ![(0 : ℂ), 2]
  have hf (i : Fin 2) : f (cX i) = ![(0 : ℂ), 2] i := by
    exact MvPolynomial.eval_X i
  intro hz
  have he := congrArg f hz
  simp only [chartDenominator, map_mul, map_sub, map_one, map_zero, hf] at he
  norm_num at he
lemma planeMap_injective : Function.Injective (planeMap p) := by
  intro a b h
  apply chartMap_injective p
  exact congrArg (fun g : C →ₐ[ℂ] L p => g a) (planeMap_comp p).symm |>.trans
    ((congrArg (fun z : B p => (z : L p)) h).trans
      (congrArg (fun g : C →ₐ[ℂ] L p => g b) (planeMap_comp p)))

def bDenominator : B p := planeMap p chartDenominator
lemma bDenominator_ne_zero : bDenominator p ≠ 0 :=
  (map_ne_zero_iff _ (planeMap_injective p)).mpr chartDenominator_ne_zero
lemma bPowers_le : Submonoid.powers (bDenominator p) ≤ (B p)⁰ := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n (bDenominator_ne_zero p))

def S := Localization.Away (bDenominator p)
instance : CommRing (S p) := inferInstanceAs (CommRing (Localization.Away (bDenominator p)))
instance : Algebra (B p) (S p) :=
  OreLocalization.instAlgebra (R := B p) (R₀ := B p)
    (S := Submonoid.powers (bDenominator p))
instance : IsLocalization.Away (bDenominator p) (S p) := Localization.isLocalization
instance : IsDomain (S p) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ (bPowers_le p)
instance : IsIntegrallyClosed (S p) :=
  isIntegrallyClosed_of_isLocalization (S p) (Submonoid.powers (bDenominator p)) (bPowers_le p)
instance : Algebra.Etale (B p) (S p) :=
  Algebra.Etale.of_isLocalizationAway (bDenominator p)
instance : IsRegularRing (S p) := EtaleRegular.regular (B p) (S p)

lemma bDenominator_unit_in_L : IsUnit (algebraMap (B p) (L p) (bDenominator p)) := by
  apply isUnit_iff_ne_zero.mpr
  exact (map_ne_zero_iff _ (Subtype.val_injective)).mpr (bDenominator_ne_zero p)

instance : Algebra (S p) (L p) :=
  (IsLocalization.Away.lift (bDenominator p) (bDenominator_unit_in_L p) : S p →+* L p).toAlgebra
instance : IsScalarTower (B p) (S p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := B p) (S := S p) (A := L p)
    (IsLocalization.Away.lift_comp (S := S p) (bDenominator p) (bDenominator_unit_in_L p)).symm
instance : Module.IsTorsionFree (S p) (L p) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  change Function.Injective (IsLocalization.Away.lift (bDenominator p) (bDenominator_unit_in_L p))
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  rw [(IsLocalization.injective (S p) (bPowers_le p)).eq_iff]
  change a = b ↔ (a : L p) = (b : L p)
  exact Subtype.val_injective.eq_iff.symm
instance : Algebra C (S p) := (algebraMap (B p) (S p)).comp (algebraMap C (B p)) |>.toAlgebra
instance : IsScalarTower C (B p) (S p) :=
  IsScalarTower.of_algebraMap_eq' (R := C) (S := B p) (A := S p) rfl
instance : IsScalarTower C (S p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := C) (S := S p) (A := L p) (by
  rw [IsScalarTower.algebraMap_eq C (B p) (L p), IsScalarTower.algebraMap_eq (B p) (S p) (L p)]
  rfl)

def remainingRoot : Fin 3 → L p := ![root p 2, root p 3, root p 4 / root p 0]
def remainingForm : Fin 3 → C := ![cX 0 - 1, cX 0 * cX 1 - 1, 1 - cX 1]
lemma remaining_dvd (i : Fin 3) : remainingForm i ∣ chartDenominator := by
  fin_cases i <;> simp only [remainingForm, chartDenominator]
  · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact dvd_mul_left _ _
lemma remaining_unit (i : Fin 3) : IsUnit (algebraMap C (S p) (remainingForm i)) :=
  IsLocalization.Away.isUnit_of_dvd (S := S p) (bDenominator p)
    (map_dvd (planeMap p) (remaining_dvd i))
lemma chartMap_X (i : Fin 2) : chartMap p (cX i) =
    ![algebraMap R (L p) (X 0),
      algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0)] i := by
  change MvPolynomial.aeval _ (X i) = _
  exact MvPolynomial.aeval_X _ _
lemma remainingRoot_pow (i : Fin 3) : remainingRoot p i ^ p =
    algebraMap C (L p) (remainingForm i) := by
  fin_cases i
  · change root p 2 ^ p = chartMap p (cX 0 - 1)
    rw [root_pow, map_sub, map_one]
    rw [chartMap_X] 
    change algebraMap R (L p) (X 0 - 1) = _
    rw [map_sub, map_one]
    rfl
  · change root p 3 ^ p = chartMap p (cX 0 * cX 1 - 1)
    rw [root_pow, map_sub, map_one, map_mul]
    rw [chartMap_X, chartMap_X]
    change algebraMap R (L p) (X 1 - 1) = algebraMap R (L p) (X 0) *
      (algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0)) - 1
    rw [map_sub, map_one]
    have hx : algebraMap R (L p) (X 0) ≠ 0 := by
      change algebraMap R (L p) (lineForm 0) ≠ 0
      rw [← root_pow p 0]
      exact pow_ne_zero _ (root_ne_zero p 0)
    rw [mul_div_cancel₀ _ hx]
  · change (root p 4 / root p 0) ^ p = chartMap p (1 - cX 1)
    rw [div_pow, root_pow, root_pow, map_sub, map_one]
    rw [chartMap_X]
    change algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0) =
      1 - algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0)
    rw [map_sub, sub_div]
    have hx : algebraMap R (L p) (X 0) ≠ 0 := by
      change algebraMap R (L p) (lineForm 0) ≠ 0
      rw [← root_pow p 0]
      exact pow_ne_zero _ (root_ne_zero p 0)
    rw [div_self hx]
lemma exponent_unit : IsUnit (p : S p) := by
  have hC : IsUnit (p : ℂ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (NeZero.ne p))
  have hB : IsUnit (p : B p) := by simpa using hC.map (algebraMap ℂ (B p))
  simpa using hB.map (algebraMap (B p) (S p))

def remainingRoots : Finset (L p) := by
  classical
  exact Finset.univ.image (fun i : Fin 3 => remainingRoot p i)
abbrev chartRootAlgebra := Algebra.adjoin (S p) (remainingRoots p : Set (L p))

theorem chartRootAlgebra_finiteFreeEtale :
    Algebra.Etale (S p) (chartRootAlgebra p) ∧
    Module.Finite (S p) (chartRootAlgebra p) ∧
    Module.Free (S p) (chartRootAlgebra p) ∧
    IsIntegrallyClosed (chartRootAlgebra p) := by
  apply KummerEtale.finite_unit_roots (R := S p) (L := L p) p
    (NeZero.pos p) (exponent_unit p) (remainingRoots p)
  intro x hx
  classical
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image _ from hx)
  refine ⟨(remaining_unit p i).unit, ?_⟩
  rw [IsUnit.unit_spec, ← IsScalarTower.algebraMap_apply C (S p) (L p)]
  exact remainingRoot_pow p i

theorem chartRootAlgebra_regular : IsRegularRing (chartRootAlgebra p) := by
  have := (chartRootAlgebra_finiteFreeEtale p).1
  exact EtaleRegular.regular (S p) (chartRootAlgebra p)
end KummerTriple

end


noncomputable section
namespace KummerEtale
variable {R K L : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L]
/-- A subalgebra of the same function field containing the original finite
field generators has that field as its fraction field. The subalgebra is
allowed to contain additional polynomial coordinates and inverted units. -/
theorem fractionRing_of_generators (C : Subalgebra R L) (s : Set L)
    (hs : Algebra.adjoin K s = ⊤) (hC : s ⊆ C) : IsFractionRing C L := by
  let g : FractionRing C →+* L := IsFractionRing.lift (g := C.val.toRingHom)
    (K := FractionRing C) Subtype.val_injective
  have hg (x : C) : g (algebraMap C (FractionRing C) x) = (x : L) :=
    IsFractionRing.lift_algebraMap Subtype.val_injective x
  have hK (x : K) : algebraMap K L x ∈ g.fieldRange := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
    rw [map_div₀]
    apply g.fieldRange.div_mem
    · refine ⟨algebraMap C (FractionRing C) (algebraMap R C a), ?_⟩
      rw [hg]
      exact IsScalarTower.algebraMap_apply R K L a
    · refine ⟨algebraMap C (FractionRing C) (algebraMap R C b), ?_⟩
      rw [hg]
      exact IsScalarTower.algebraMap_apply R K L b
  let D : Subalgebra K L := { g.fieldRange.toSubring with algebraMap_mem' := hK }
  have hD : Algebra.adjoin K s ≤ D := by
    refine Algebra.adjoin_le ?_
    intro x hx
    exact ⟨algebraMap C (FractionRing C) ⟨x, hC hx⟩, hg _⟩
  have hsurj : Function.Surjective g := by
    intro x
    exact hD (by rw [hs]; trivial)
  have : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).mpr
    Subtype.val_injective
  apply IsFractionRing.of_field
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective C y
  exact ⟨a, b, by rw [map_div₀, hg, hg]; rfl⟩
end KummerEtale


open Algebra MvPolynomial
open nonZeroDivisors
namespace KummerTriple
open KummerLines
variable (p : ℕ) [Fact p.Prime]
instance : IsDomain C := inferInstanceAs (IsDomain (MvPolynomial (Fin 2) ℂ))
instance : Module.IsTorsionFree C (L p) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (chartMap_injective p)

/-- The actual open D((s−1)(st−1)(1−t)) of the blowup chart. -/
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
  · exact coordinateRoot_mem_chartRootAlgebra p 0
  · change root p 1 ∈ chartRootAlgebra p
    rw [original_root_one p]
    exact Subalgebra.mul_mem _ (coordinateRoot_mem_chartRootAlgebra p 0)
      (coordinateRoot_mem_chartRootAlgebra p 1)
  · exact remainingRoot_mem_chartRootAlgebra p 0
  · exact remainingRoot_mem_chartRootAlgebra p 1
  · change root p 4 ∈ chartRootAlgebra p
    have he : root p 4 = coordinateRoot p 0 * remainingRoot p 2 := by
      change root p 4 = root p 0 * (root p 4 / root p 0)
      exact (mul_div_cancel₀ _ (root_ne_zero p 0)).symm
    rw [he]
    exact Subalgebra.mul_mem _ (coordinateRoot_mem_chartRootAlgebra p 0)
      (remainingRoot_mem_chartRootAlgebra p 2)

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
end KummerTriple


end


section

noncomputable section

namespace ExplicitCone
open scoped BigOperators
open Polynomial
abbrev L := KummerLines.L 7
abbrev R := KummerLines.R
abbrev K := KummerLines.K
abbrev y (i : Fin 5) : L := KummerCover.fieldRoot (p := 7) KummerLines.radicand i

def z : Fin 6 → L := Fin.cases 1 y

def pairs : Fin 3 → Fin 6 × Fin 6 := ![(1, 4), (2, 3), (5, 0)]

lemma y_ne_zero (i : Fin 5) : y i ≠ 0 := by
  intro h
  have hh := KummerCover.fieldRoot_pow (p := 7) KummerLines.radicand i
  change y i ^ 7 = algebraMap K L (KummerLines.radicand i) at hh
  rw [h, zero_pow (by decide : 7 ≠ 0)] at hh
  have hr : KummerLines.radicand i ≠ 0 := by
    simpa only [KummerLines.radicand, map_zero] using
      (IsFractionRing.injective R K).ne (KummerLines.prime_lineForm i).ne_zero
  exact hr ((algebraMap K L).injective (by simpa using hh.symm))

lemma z_ne_zero (i : Fin 6) : z i ≠ 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [z]
  · exact y_ne_zero j

lemma roots_generate_over_complex : IntermediateField.adjoin ℂ (Set.range y) = ⊤ := by
  let S := IntermediateField.adjoin ℂ (Set.range y)
  have hymem (i : Fin 5) : y i ∈ S := IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have hx (i : Fin 2) : algebraMap R L (MvPolynomial.X i) ∈ S := by
    fin_cases i
    · have hh := pow_mem (hymem 0) 7
      have he : y 0 ^ 7 = algebraMap R L (MvPolynomial.X 0) := by
        rw [KummerCover.fieldRoot_pow]
        exact (IsScalarTower.algebraMap_apply R K L (MvPolynomial.X 0)).symm
      exact he ▸ hh
    · have hh := pow_mem (hymem 1) 7
      have he : y 1 ^ 7 = algebraMap R L (MvPolynomial.X 1) := by
        rw [KummerCover.fieldRoot_pow]
        exact (IsScalarTower.algebraMap_apply R K L (MvPolynomial.X 1)).symm
      exact he ▸ hh
  have hR (a : R) : algebraMap R L a ∈ S := by
    induction a using MvPolynomial.induction_on with
    | C c => exact S.algebraMap_mem c
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | mul_X p i hp => simpa only [map_mul] using S.mul_mem hp (hx i)
  have hK (a : K) : algebraMap K L a ∈ S := by
    obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective R a
    simpa only [map_div₀, ← IsScalarTower.algebraMap_apply] using S.div_mem (hR p) (hR q)
  apply top_unique
  intro a ha
  clear ha
  have hh : a ∈ Algebra.adjoin K (Set.range y) := by
    rw [KummerCover.fieldRoot_generates]; trivial
  induction hh using Algebra.adjoin_induction with
  | mem a ha => exact IntermediateField.subset_adjoin ℂ _ ha
  | algebraMap a => exact hK a
  | add a b ha hb h₁ h₂ => exact S.add_mem h₁ h₂
  | mul a b ha hb h₁ h₂ => exact S.mul_mem h₁ h₂

/-- The eighteen degree-one sections in the chosen rational trivialization of H.
The original y-indexing is shifted by one, so z₀=1 is the sixth line. -/
def sectionCoefficient (i : Fin 6 × Fin 3) : L :=
  z i.1 * z (pairs i.2).1 * z (pairs i.2).2

def generator (i : Fin 6 × Fin 3) : RatFunc L :=
  RatFunc.C (sectionCoefficient i) * RatFunc.X

abbrev algebra := Algebra.adjoin ℂ (Set.range generator)

instance finiteType : Algebra.FiniteType ℂ algebra :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range generator)

instance noetherian : IsNoetherianRing algebra := Algebra.FiniteType.isNoetherianRing ℂ algebra

lemma generators_field : IntermediateField.adjoin ℂ (Set.range generator) = ⊤ := by
  let S := IntermediateField.adjoin ℂ (Set.range generator)
  have hg (i : Fin 6 × Fin 3) : generator i ∈ S :=
    IntermediateField.subset_adjoin ℂ _ ⟨i, rfl⟩
  have hc (i : Fin 6) : RatFunc.C (z i) ∈ S := by
    have hu : (RatFunc.C (z (pairs 0).1 * z (pairs 0).2) * RatFunc.X : RatFunc L) ≠ 0 :=
      mul_ne_zero ((by simpa only [map_zero] using RatFunc.C_injective.ne (mul_ne_zero (z_ne_zero (pairs 0).1) (z_ne_zero (pairs 0).2))))
        RatFunc.X_ne_zero
    have hh : RatFunc.C (z i) = generator (i, 0) / generator (0, 0) := by
      change RatFunc.C (z i) =
        (RatFunc.C (z i * z (pairs 0).1 * z (pairs 0).2) * RatFunc.X) /
        (RatFunc.C (1 * z (pairs 0).1 * z (pairs 0).2) * RatFunc.X)
      apply (eq_div_iff (by simpa only [one_mul] using hu)).mpr
      simp only [one_mul, map_mul]
      ring
    rw [hh]
    exact S.div_mem (hg (i, 0)) (hg (0, 0))
  have hCL (a : L) : RatFunc.C a ∈ S := by
    have hroot : IntermediateField.adjoin ℂ (Set.range y) ≤ S.comap (IsScalarTower.toAlgHom ℂ L (RatFunc L)) := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i, rfl⟩
      exact hc i.succ
    rw [roots_generate_over_complex] at hroot
    exact hroot (show a ∈ (⊤ : IntermediateField ℂ L) from trivial)
  have hX : (RatFunc.X : RatFunc L) ∈ S := by
    have hn : RatFunc.C (z (pairs 0).1 * z (pairs 0).2) ≠ (0 : RatFunc L) :=
      (by simpa only [map_zero] using RatFunc.C_injective.ne (mul_ne_zero (z_ne_zero (pairs 0).1) (z_ne_zero (pairs 0).2)))
    have he : (RatFunc.X : RatFunc L) = generator (0, 0) / RatFunc.C (z (pairs 0).1 * z (pairs 0).2) := by
      change RatFunc.X = RatFunc.C (1 * z (pairs 0).1 * z (pairs 0).2) * RatFunc.X /
        RatFunc.C (z (pairs 0).1 * z (pairs 0).2)
      simp only [one_mul]
      rw [mul_div_cancel_left₀ _ hn]
    rw [he]
    exact S.div_mem (hg (0, 0)) (hCL _)
  have hP (p : L[X]) : algebraMap L[X] (RatFunc L) p ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X]
      exact S.mul_mem (hCL a) (pow_mem hX n)
  apply top_unique
  intro a _
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective L[X] a
  exact S.div_mem (hP p) (hP q)

instance fractionRing : IsFractionRing algebra (RatFunc L) :=
  IsFractionRing.of_field algebra (RatFunc L) fun a => by
    have ha : a ∈ IntermediateField.adjoin ℂ (Set.range generator) := by
      rw [generators_field]; trivial
    obtain ⟨x, hx, y, hy, h⟩ := IntermediateField.mem_adjoin_iff_div.mp ha
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, h⟩

end ExplicitCone

end


noncomputable section
namespace ExplicitCone
open MvPolynomial

/-- The literal affine coordinate functions for the degree-one section
z₀z₁z₄ in the fixed H=3J−E linear system. -/
def sectionRatio (i : Fin 6 × Fin 3) : L :=
  sectionCoefficient i / sectionCoefficient (0, 0)
def sectionChart : Subalgebra ℂ L := Algebra.adjoin ℂ (Set.range sectionRatio)
def ratioQ : L := y 1 * y 2 / (y 0 * y 3)
def ratioR : L := y 4 / (y 0 * y 3)

lemma sectionCoefficient_base : sectionCoefficient (0, 0) = y 0 * y 3 := by
  change 1 * y 0 * y 3 = y 0 * y 3
  rw [one_mul]
lemma sectionCoefficient_base_ne_zero : sectionCoefficient (0, 0) ≠ 0 := by
  rw [sectionCoefficient_base]
  exact mul_ne_zero (y_ne_zero 0) (y_ne_zero 3)
lemma sectionRatio_zero (i : Fin 6) : sectionRatio (i, 0) = z i := by
  unfold sectionRatio
  rw [sectionCoefficient_base]
  change z i * y 0 * y 3 / (y 0 * y 3) = z i
  rw [mul_assoc, mul_div_cancel_right₀ _ (mul_ne_zero (y_ne_zero 0) (y_ne_zero 3))]
lemma sectionRatio_one (i : Fin 6) : sectionRatio (i, 1) = z i * ratioQ := by
  unfold sectionRatio ratioQ
  rw [sectionCoefficient_base]
  change z i * y 1 * y 2 / (y 0 * y 3) = _
  ring
lemma sectionRatio_two (i : Fin 6) : sectionRatio (i, 2) = z i * ratioR := by
  unfold sectionRatio ratioR
  rw [sectionCoefficient_base]
  change z i * y 4 * 1 / (y 0 * y 3) = _
  ring
lemma y_mem_sectionChart (i : Fin 5) : y i ∈ sectionChart := by
  have h : sectionRatio (i.succ, 0) ∈ sectionChart :=
    Algebra.subset_adjoin (Set.mem_range_self _)
  simpa only [sectionRatio_zero, z, Fin.cases_succ] using h
lemma ratioQ_mem_sectionChart : ratioQ ∈ sectionChart := by
  have h : sectionRatio (0, 1) ∈ sectionChart :=
    Algebra.subset_adjoin (Set.mem_range_self _)
  simpa only [sectionRatio_one, z, Fin.cases_zero, one_mul] using h
lemma ratioR_mem_sectionChart : ratioR ∈ sectionChart := by
  have h : sectionRatio (0, 2) ∈ sectionChart :=
    Algebra.subset_adjoin (Set.mem_range_self _)
  simpa only [sectionRatio_two, z, Fin.cases_zero, one_mul] using h

/-- Equality for the actual coefficient ratios, with no change of roots,
polarization, field, or exponent. -/
theorem sectionChart_eq : sectionChart =
    Algebra.adjoin ℂ (Set.range y ∪ {ratioQ, ratioR}) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨⟨i,j⟩, rfl⟩
    have hi : z i ∈ Algebra.adjoin ℂ (Set.range y ∪ {ratioQ, ratioR}) := by
      refine Fin.cases ?_ (fun k => ?_) i
      · exact Subalgebra.one_mem _
      · exact Algebra.subset_adjoin (Or.inl (Set.mem_range_self k))
    have hq : ratioQ ∈ Algebra.adjoin ℂ (Set.range y ∪ {ratioQ, ratioR}) :=
      Algebra.subset_adjoin (Or.inr (by simp))
    have hr : ratioR ∈ Algebra.adjoin ℂ (Set.range y ∪ {ratioQ, ratioR}) :=
      Algebra.subset_adjoin (Or.inr (by simp))
    fin_cases j
    · change sectionRatio (i, 0) ∈ _
      rw [sectionRatio_zero]; exact hi
    · change sectionRatio (i, 1) ∈ _
      rw [sectionRatio_one]; exact Subalgebra.mul_mem _ hi hq
    · change sectionRatio (i, 2) ∈ _
      rw [sectionRatio_two]; exact Subalgebra.mul_mem _ hi hr
  · apply Algebra.adjoin_le
    rintro t (⟨i,rfl⟩ | ht)
    · exact y_mem_sectionChart i
    · rcases (show t = ratioQ ∨ t = ratioR from by simpa using ht) with rfl | rfl
      · exact ratioQ_mem_sectionChart
      · exact ratioR_mem_sectionChart

/-- The two redundant-looking coordinates record the resolved triple
points, and the Fermat identity guarantees their opens cover. -/
lemma ratioQ_product : y 0 * y 3 * ratioQ = y 1 * y 2 := by
  exact mul_div_cancel₀ _ (mul_ne_zero (y_ne_zero 0) (y_ne_zero 3))
lemma ratioR_product : y 0 * y 3 * ratioR = y 4 := by
  exact mul_div_cancel₀ _ (mul_ne_zero (y_ne_zero 0) (y_ne_zero 3))
lemma y_power (i : Fin 5) : y i ^ 7 = algebraMap R L (KummerLines.lineForm i) := by
  rw [KummerCover.fieldRoot_pow]
  exact (IsScalarTower.algebraMap_apply R K L _).symm
lemma y_power_zero : y 0 ^ 7 = algebraMap R L (X 0) := y_power 0
lemma y_power_one : y 1 ^ 7 = algebraMap R L (X 1) := y_power 1
lemma y_power_two : y 2 ^ 7 = algebraMap R L (X 0) - 1 := by
  have h := y_power 2
  change y 2 ^ 7 = algebraMap R L (X 0 - 1) at h
  simpa only [map_sub, map_one] using h
lemma y_power_three : y 3 ^ 7 = algebraMap R L (X 1) - 1 := by
  simpa [KummerLines.lineForm, map_sub, map_one] using y_power 3
lemma y_power_four : y 4 ^ 7 = algebraMap R L (X 0) - algebraMap R L (X 1) := by
  simpa [KummerLines.lineForm, map_sub] using y_power 4
lemma ratioQ_power : ratioQ ^ 7 =
    algebraMap R L (X 1) * (algebraMap R L (X 0) - 1) /
      (algebraMap R L (X 0) * (algebraMap R L (X 1) - 1)) := by
  rw [ratioQ, div_pow, mul_pow, mul_pow, y_power_zero, y_power_one,
    y_power_two, y_power_three]
lemma ratioR_power : ratioR ^ 7 =
    (algebraMap R L (X 0) - algebraMap R L (X 1)) /
      (algebraMap R L (X 0) * (algebraMap R L (X 1) - 1)) := by
  rw [ratioR, div_pow, mul_pow, y_power_zero, y_power_three, y_power_four]
lemma ratio_fermat : ratioQ ^ 7 - ratioR ^ 7 = 1 := by
  rw [ratioQ_power, ratioR_power, ← sub_div]
  have h0 : algebraMap R L (X 0) ≠ 0 := by
    rw [← y_power_zero]; exact pow_ne_zero _ (y_ne_zero 0)
  have h1 : algebraMap R L (X 1) - 1 ≠ 0 := by
    rw [← y_power_three]; exact pow_ne_zero _ (y_ne_zero 3)
  rw [div_eq_one_iff_eq (mul_ne_zero h0 h1)]
  ring

/-- Six functions suffice: the fifth original root is reconstructed. -/
def chartCoordinates : Fin 6 → L := ![y 0, y 1, y 2, y 3, ratioQ, ratioR]
lemma chartCoordinates_mem (i : Fin 6) : chartCoordinates i ∈ sectionChart := by
  fin_cases i
  · exact y_mem_sectionChart 0
  · exact y_mem_sectionChart 1
  · exact y_mem_sectionChart 2
  · exact y_mem_sectionChart 3
  · exact ratioQ_mem_sectionChart
  · exact ratioR_mem_sectionChart

theorem sectionChart_eq_six : sectionChart = Algebra.adjoin ℂ (Set.range chartCoordinates) := by
  apply le_antisymm
  · rw [sectionChart_eq]
    apply Algebra.adjoin_le
    have hm (i : Fin 6) : chartCoordinates i ∈ Algebra.adjoin ℂ (Set.range chartCoordinates) :=
      Algebra.subset_adjoin (Set.mem_range_self i)
    rintro t (⟨i,rfl⟩ | ht)
    · fin_cases i
      · exact hm 0
      · exact hm 1
      · exact hm 2
      · exact hm 3
      · change y 4 ∈ _
        rw [← ratioR_product]
        exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hm 0) (hm 3)) (hm 5)
    · rcases (show t = ratioQ ∨ t = ratioR from by simpa using ht) with rfl | rfl
      · exact hm 4
      · exact hm 5
  · exact Algebra.adjoin_le (by rintro _ ⟨i,rfl⟩; exact chartCoordinates_mem i)

instance sectionChart_finiteType : Algebra.FiniteType ℂ sectionChart := by
  rw [sectionChart_eq_six]
  exact Algebra.FiniteType.adjoin_of_finite (Set.finite_range chartCoordinates)

instance sectionChart_fractionRing : IsFractionRing sectionChart L :=
  IsFractionRing.of_field sectionChart L fun t => by
    have ht : t ∈ IntermediateField.adjoin ℂ (Set.range y) := by
      rw [roots_generate_over_complex]; trivial
    obtain ⟨a,ha,b,hb,h⟩ := IntermediateField.mem_adjoin_iff_div.mp ht
    have hle : Algebra.adjoin ℂ (Set.range y) ≤ sectionChart :=
      Algebra.adjoin_le (by rintro _ ⟨i,rfl⟩; exact y_mem_sectionChart i)
    exact ⟨⟨a,hle ha⟩,⟨b,hle hb⟩,h⟩

end ExplicitCone

end

end


noncomputable section
open nonZeroDivisors
namespace FieldPrincipalOpen
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
variable (A : Subalgebra k L) [IsFractionRing A L] (d : A) (hd : d ≠ 0)

include hd in
omit [IsFractionRing A L] in
lemma powers_le : Submonoid.powers d ≤ A⁰ := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hd)

/-- A principal open as an actual subalgebra of the fixed function field. -/
def away : Subalgebra k L :=
  (Localization.subalgebra.ofField L (Submonoid.powers d) (powers_le A d hd)).restrictScalars k

instance : Algebra A (away A d hd) :=
  inferInstanceAs (Algebra A (Localization.subalgebra.ofField L (Submonoid.powers d)
    (powers_le A d hd)))
instance : IsLocalization.Away d (away A d hd) :=
  inferInstanceAs (IsLocalization.Away d (Localization.subalgebra.ofField L (Submonoid.powers d)
    (powers_le A d hd)))

lemma mem_away_iff (x : L) : x ∈ away A d hd ↔
    ∃ (a : A) (n : ℕ), x = (a : L) / (d : L) ^ n := by
  change (∃ (a s : A) (_ : s ∈ Submonoid.powers d),
    x = (a : L) * (s : L)⁻¹) ↔ _
  constructor
  · rintro ⟨a, _, ⟨n,rfl⟩, h⟩
    exact ⟨a,n,by simpa only [Subalgebra.coe_pow, div_eq_mul_inv] using h⟩
  · rintro ⟨a,n,h⟩
    exact ⟨a,d ^ n,⟨n,rfl⟩,by simpa only [Subalgebra.coe_pow, div_eq_mul_inv] using h⟩

lemma le_away : A ≤ away A d hd := by
  intro a ha
  exact (mem_away_iff A d hd a).mpr ⟨⟨a,ha⟩,0,by simp⟩
lemma inv_mem_away : (d : L)⁻¹ ∈ away A d hd := by
  exact (mem_away_iff A d hd _).mpr ⟨1,1,by simp⟩

lemma away_le_iff (B : Subalgebra k L) : away A d hd ≤ B ↔
    A ≤ B ∧ (d : L)⁻¹ ∈ B := by
  constructor
  · intro h
    exact ⟨(le_away A d hd).trans h, h (inv_mem_away A d hd)⟩
  · rintro ⟨hA,hd'⟩ x hx
    obtain ⟨a,n,rfl⟩ := (mem_away_iff A d hd x).mp hx
    rw [div_eq_mul_inv, ← inv_pow]
    exact B.mul_mem (hA a.property) (B.pow_mem hd' n)

lemma away_eq_adjoin : away A d hd = Algebra.adjoin k ((A : Set L) ∪ {(d : L)⁻¹}) := by
  apply le_antisymm
  · apply (away_le_iff A d hd _).mpr
    exact ⟨fun _ hx => Algebra.subset_adjoin (Or.inl hx),
      Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))⟩
  · apply Algebra.adjoin_le
    rintro x (hx | hx)
    · exact le_away A d hd hx
    · exact (Set.mem_singleton_iff.mp hx) ▸ inv_mem_away A d hd

lemma regular_away_of_eq (B : Subalgebra k L) [IsRegularRing B]
    (h : away A d hd = B) : IsRegularRing (Localization.Away d) := by
  have : IsRegularRing (away A d hd) :=
    IsRegularRing.of_ringEquiv (Subalgebra.equivOfEq _ _ h.symm).toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (IsLocalization.algEquiv (Submonoid.powers d) (away A d hd) (Localization.Away d)).toRingEquiv

end FieldPrincipalOpen

end


noncomputable section
open Algebra MvPolynomial
namespace KummerTriple
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
end KummerTriple

namespace FieldPrincipalOpen
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
lemma inv_left_mem (A : Subalgebra k L) {x y : L} (hy : y ≠ 0)
    (hyA : y ∈ A) (hi : (x * y)⁻¹ ∈ A) : x⁻¹ ∈ A := by
  have h := A.mul_mem hi hyA
  have he : (x * y)⁻¹ * y = x⁻¹ := by
    simp [mul_inv_rev, mul_assoc, mul_left_comm, hy]
  exact he ▸ h

lemma localizationImage_mem {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (A : Subalgebra k L) (d : R) [IsLocalization.Away d S]
    (hd : algebraMap R L d ≠ 0)
    (hR : ∀ a : R, algebraMap R L a ∈ A)
    (hi : (algebraMap R L d)⁻¹ ∈ A) (s : S) : algebraMap S L s ∈ A := by
  obtain ⟨n,a,h⟩ := IsLocalization.Away.surj d s
  have he := congrArg (algebraMap S L) h
  simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at he
  have he' : algebraMap S L s = algebraMap R L a / (algebraMap R L d) ^ n :=
    (eq_div_iff (pow_ne_zero n hd)).mpr he
  rw [he', div_eq_mul_inv, ← inv_pow]
  exact A.mul_mem (hR a) (A.pow_mem hi n)
end FieldPrincipalOpen

namespace ExplicitCone

lemma ratioR_ne_zero : ratioR ≠ 0 :=
  div_ne_zero (y_ne_zero 4) (mul_ne_zero (y_ne_zero 0) (y_ne_zero 3))
lemma ratioQ_ne_zero : ratioQ ≠ 0 :=
  div_ne_zero (mul_ne_zero (y_ne_zero 1) (y_ne_zero 2))
    (mul_ne_zero (y_ne_zero 0) (y_ne_zero 3))

def tripleSectionDenominator : sectionChart :=
  ⟨y 2 * y 3 * ratioR, sectionChart.mul_mem
    (sectionChart.mul_mem (y_mem_sectionChart 2) (y_mem_sectionChart 3)) ratioR_mem_sectionChart⟩
lemma tripleSectionDenominator_ne_zero : tripleSectionDenominator ≠ 0 := by
  intro h
  exact mul_ne_zero (mul_ne_zero (y_ne_zero 2) (y_ne_zero 3)) ratioR_ne_zero
    (congrArg Subtype.val h)
def tripleSectionOpen : Subalgebra ℂ L :=
  FieldPrincipalOpen.away sectionChart tripleSectionDenominator tripleSectionDenominator_ne_zero

def tripleRegularAlgebra : Subalgebra ℂ L where
  toSubsemiring := (KummerTriple.chartRootAlgebra 7).toSubsemiring
  algebraMap_mem' c := by
    have h := (KummerTriple.chartRootAlgebra 7).algebraMap_mem
      (algebraMap (KummerTriple.B 7) (KummerTriple.S 7)
        (algebraMap ℂ (KummerTriple.B 7) c))
    rw [← IsScalarTower.algebraMap_apply (KummerTriple.B 7) (KummerTriple.S 7) L] at h
    exact h

lemma y_mem_tripleRegular (i : Fin 5) : y i ∈ tripleRegularAlgebra :=
  KummerTriple.allRoots_mem_chartRootAlgebra 7 i
lemma unitRoot_inv_mem_tripleRegular (i : Fin 3) :
    (KummerTriple.remainingRoot 7 i)⁻¹ ∈ tripleRegularAlgebra :=
  KummerTriple.remainingRoot_inv_mem 7 i

lemma ratioQ_mem_tripleRegular : ratioQ ∈ tripleRegularAlgebra := by
  have h0 : y 1 / y 0 ∈ tripleRegularAlgebra :=
    KummerTriple.coordinateRoot_mem_chartRootAlgebra 7 1
  have h1 : (y 3)⁻¹ ∈ tripleRegularAlgebra := unitRoot_inv_mem_tripleRegular 1
  have he : ratioQ = (y 1 / y 0) * y 2 * (y 3)⁻¹ := by
    unfold ratioQ
    field_simp [y_ne_zero]
  rw [he]
  exact tripleRegularAlgebra.mul_mem
    (tripleRegularAlgebra.mul_mem h0 (y_mem_tripleRegular 2)) h1
lemma ratioR_mem_tripleRegular : ratioR ∈ tripleRegularAlgebra := by
  have h0 : y 4 / y 0 ∈ tripleRegularAlgebra :=
    KummerTriple.remainingRoot_mem_chartRootAlgebra 7 2
  have h1 : (y 3)⁻¹ ∈ tripleRegularAlgebra := unitRoot_inv_mem_tripleRegular 1
  have he : ratioR = (y 4 / y 0) * (y 3)⁻¹ := by
    unfold ratioR
    field_simp [y_ne_zero]
  rw [he]
  exact tripleRegularAlgebra.mul_mem h0 h1
lemma sectionChart_le_tripleRegular : sectionChart ≤ tripleRegularAlgebra := by
  rw [sectionChart_eq]
  apply Algebra.adjoin_le
  rintro t (⟨i,rfl⟩ | ht)
  · exact y_mem_tripleRegular i
  · rcases (show t = ratioQ ∨ t = ratioR from by simpa using ht) with rfl | rfl
    · exact ratioQ_mem_tripleRegular
    · exact ratioR_mem_tripleRegular
lemma ratioR_inv_mem_tripleRegular : ratioR⁻¹ ∈ tripleRegularAlgebra := by
  have h0 : (y 4 / y 0)⁻¹ ∈ tripleRegularAlgebra := unitRoot_inv_mem_tripleRegular 2
  have he : ratioR⁻¹ = (y 4 / y 0)⁻¹ * y 3 := by
    unfold ratioR
    field_simp [y_ne_zero]
  rw [he]
  exact tripleRegularAlgebra.mul_mem h0 (y_mem_tripleRegular 3)
lemma tripleSectionOpen_le : tripleSectionOpen ≤ tripleRegularAlgebra := by
  apply (FieldPrincipalOpen.away_le_iff sectionChart tripleSectionDenominator
    tripleSectionDenominator_ne_zero tripleRegularAlgebra).mpr
  refine ⟨sectionChart_le_tripleRegular, ?_⟩
  change (y 2 * y 3 * ratioR)⁻¹ ∈ tripleRegularAlgebra
  rw [mul_inv_rev, mul_inv_rev]
  exact tripleRegularAlgebra.mul_mem ratioR_inv_mem_tripleRegular
    (tripleRegularAlgebra.mul_mem (unitRoot_inv_mem_tripleRegular 1)
      (unitRoot_inv_mem_tripleRegular 0))

lemma sectionChart_le_tripleOpen : sectionChart ≤ tripleSectionOpen :=
  FieldPrincipalOpen.le_away sectionChart tripleSectionDenominator tripleSectionDenominator_ne_zero
lemma y_mem_tripleOpen (i : Fin 5) : y i ∈ tripleSectionOpen :=
  sectionChart_le_tripleOpen (y_mem_sectionChart i)
lemma ratioQ_mem_tripleOpen : ratioQ ∈ tripleSectionOpen :=
  sectionChart_le_tripleOpen ratioQ_mem_sectionChart
lemma ratioR_mem_tripleOpen : ratioR ∈ tripleSectionOpen :=
  sectionChart_le_tripleOpen ratioR_mem_sectionChart
lemma tripleProduct_inv_mem : (y 2 * y 3 * ratioR)⁻¹ ∈ tripleSectionOpen :=
  FieldPrincipalOpen.inv_mem_away sectionChart tripleSectionDenominator tripleSectionDenominator_ne_zero
lemma y2_inv_mem_tripleOpen : (y 2)⁻¹ ∈ tripleSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem tripleSectionOpen
    (mul_ne_zero (y_ne_zero 3) ratioR_ne_zero)
    (tripleSectionOpen.mul_mem (y_mem_tripleOpen 3) ratioR_mem_tripleOpen)
  simpa only [mul_assoc] using tripleProduct_inv_mem
lemma y3_inv_mem_tripleOpen : (y 3)⁻¹ ∈ tripleSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem tripleSectionOpen
    (mul_ne_zero (y_ne_zero 2) ratioR_ne_zero)
    (tripleSectionOpen.mul_mem (y_mem_tripleOpen 2) ratioR_mem_tripleOpen)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using tripleProduct_inv_mem
lemma ratioR_inv_mem_tripleOpen : ratioR⁻¹ ∈ tripleSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem tripleSectionOpen
    (mul_ne_zero (y_ne_zero 2) (y_ne_zero 3))
    (tripleSectionOpen.mul_mem (y_mem_tripleOpen 2) (y_mem_tripleOpen 3))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using tripleProduct_inv_mem

lemma coordinateRoot_mem_tripleOpen (i : Fin 2) :
    KummerTriple.coordinateRoot 7 i ∈ tripleSectionOpen := by
  fin_cases i
  · exact y_mem_tripleOpen 0
  · change y 1 / y 0 ∈ tripleSectionOpen
    have he : y 1 / y 0 = ratioQ * y 3 * (y 2)⁻¹ := by
      unfold ratioQ
      field_simp [y_ne_zero]
    rw [he]
    exact tripleSectionOpen.mul_mem
      (tripleSectionOpen.mul_mem ratioQ_mem_tripleOpen (y_mem_tripleOpen 3))
      y2_inv_mem_tripleOpen
lemma B_mem_tripleOpen (b : KummerTriple.B 7) : (b : L) ∈ tripleSectionOpen := by
  have h := b.property
  change (b : L) ∈ Algebra.adjoin ℂ (Set.range (KummerTriple.coordinateRoot 7)) at h
  exact (Algebra.adjoin_le (by rintro _ ⟨i,rfl⟩; exact coordinateRoot_mem_tripleOpen i)) h
lemma remainingRoot_mem_tripleOpen (i : Fin 3) :
    KummerTriple.remainingRoot 7 i ∈ tripleSectionOpen := by
  fin_cases i
  · exact y_mem_tripleOpen 2
  · exact y_mem_tripleOpen 3
  · change y 4 / y 0 ∈ tripleSectionOpen
    have he : y 4 / y 0 = ratioR * y 3 := by
      unfold ratioR
      field_simp [y_ne_zero]
    rw [he]
    exact tripleSectionOpen.mul_mem ratioR_mem_tripleOpen (y_mem_tripleOpen 3)
lemma remainingRoot_inv_mem_tripleOpen (i : Fin 3) :
    (KummerTriple.remainingRoot 7 i)⁻¹ ∈ tripleSectionOpen := by
  fin_cases i
  · exact y2_inv_mem_tripleOpen
  · exact y3_inv_mem_tripleOpen
  · change (y 4 / y 0)⁻¹ ∈ tripleSectionOpen
    have he : (y 4 / y 0)⁻¹ = ratioR⁻¹ * (y 3)⁻¹ := by
      unfold ratioR
      field_simp [y_ne_zero]
    rw [he]
    exact tripleSectionOpen.mul_mem ratioR_inv_mem_tripleOpen y3_inv_mem_tripleOpen

lemma bDenominator_image :
    algebraMap (KummerTriple.B 7) L (KummerTriple.bDenominator 7) =
    KummerTriple.remainingRoot 7 0 ^ 7 * KummerTriple.remainingRoot 7 1 ^ 7 *
      KummerTriple.remainingRoot 7 2 ^ 7 := by
  change algebraMap (KummerTriple.B 7) L
    (algebraMap KummerTriple.C (KummerTriple.B 7) KummerTriple.chartDenominator) = _
  rw [← IsScalarTower.algebraMap_apply KummerTriple.C (KummerTriple.B 7) L]
  change algebraMap KummerTriple.C L
    (KummerTriple.remainingForm 0 * KummerTriple.remainingForm 1 * KummerTriple.remainingForm 2) = _
  simp only [map_mul, KummerTriple.remainingRoot_pow]
lemma bDenominator_inv_mem_tripleOpen :
    (algebraMap (KummerTriple.B 7) L (KummerTriple.bDenominator 7))⁻¹ ∈ tripleSectionOpen := by
  rw [bDenominator_image, mul_inv_rev, mul_inv_rev, ← inv_pow, ← inv_pow, ← inv_pow]
  exact tripleSectionOpen.mul_mem (tripleSectionOpen.pow_mem (remainingRoot_inv_mem_tripleOpen 2) 7)
    (tripleSectionOpen.mul_mem (tripleSectionOpen.pow_mem (remainingRoot_inv_mem_tripleOpen 1) 7)
      (tripleSectionOpen.pow_mem (remainingRoot_inv_mem_tripleOpen 0) 7))
lemma S_mem_tripleOpen (s : KummerTriple.S 7) :
    algebraMap (KummerTriple.S 7) L s ∈ tripleSectionOpen := by
  apply FieldPrincipalOpen.localizationImage_mem tripleSectionOpen (KummerTriple.bDenominator 7)
    ((isUnit_iff_ne_zero).mp (KummerTriple.bDenominator_unit_in_L 7))
    (fun b => B_mem_tripleOpen b) bDenominator_inv_mem_tripleOpen
lemma tripleRegular_le_sectionOpen : tripleRegularAlgebra ≤ tripleSectionOpen := by
  intro t ht
  change t ∈ Algebra.adjoin (KummerTriple.S 7) (KummerTriple.remainingRoots 7 : Set L) at ht
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    classical
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image _ from hx)
    exact remainingRoot_mem_tripleOpen i
  | algebraMap s => exact S_mem_tripleOpen s
  | add x y hx hy h₁ h₂ => exact tripleSectionOpen.add_mem h₁ h₂
  | mul x y hx hy h₁ h₂ => exact tripleSectionOpen.mul_mem h₁ h₂

/-- The literal polarization chart, localized at c*d*r, is exactly the
regular normalization of the literal triple-point blowup open, within the
same original function field. -/
theorem tripleSectionOpen_eq : tripleSectionOpen = tripleRegularAlgebra :=
  le_antisymm tripleSectionOpen_le tripleRegular_le_sectionOpen

theorem sectionChart_tripleOpen_regular :
    IsRegularRing (Localization.Away tripleSectionDenominator) := by
  have : IsRegularRing tripleRegularAlgebra := KummerTriple.chartRootAlgebra_regular 7
  exact FieldPrincipalOpen.regular_away_of_eq sectionChart tripleSectionDenominator
    tripleSectionDenominator_ne_zero tripleRegularAlgebra tripleSectionOpen_eq

end ExplicitCone

end

end OAI
