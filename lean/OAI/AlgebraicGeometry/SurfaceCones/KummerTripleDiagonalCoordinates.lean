import OAI.AlgebraicGeometry.SurfaceCones.KummerTripleOpen

namespace OAI

noncomputable section
open Algebra MvPolynomial
namespace KummerTripleDiagonal
open KummerLines
variable (p : ℕ) [Fact p.Prime]
local instance : IsScalarTower ℂ R (L p) := IsScalarTower.of_algebraMap_eq' rfl

abbrev root (i : Fin 5) : L p := KummerCover.fieldRoot (p := p) radicand i
lemma root_pow (i : Fin 5) : root p i ^ p = algebraMap R (L p) (lineForm i) :=
  KummerCover.fieldRoot_pow radicand i
lemma root_ne_zero (i : Fin 5) : root p i ≠ 0 := by
  intro h
  have hz := root_pow p i
  rw [h, zero_pow (NeZero.ne p)] at hz
  have hi : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  exact (prime_lineForm i).ne_zero (hi (hz.symm.trans (map_zero (algebraMap R (L p))).symm))

/-- Coordinates at the exceptional divisor over the actual triple point
(0,0): u is the original root of x, v is root(x−y)/root(x). -/
def coordinateRoot : Fin 2 → L p := ![root p 0, root p 4 / root p 0]
lemma coordinateRoot_zero_pow : coordinateRoot p 0 ^ p = algebraMap R (L p) (X 0) :=
  root_pow p 0
lemma coordinateRoot_one_pow : coordinateRoot p 1 ^ p =
    algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0) := by
  change (root p 4 / root p 0) ^ p = _
  rw [div_pow, root_pow, root_pow]
  rfl
lemma original_root_one : root p 4 = coordinateRoot p 0 * coordinateRoot p 1 := by
  change root p 4 = root p 0 * (root p 4 / root p 0)
  field_simp [root_ne_zero p 0]

lemma coordinateRoot_independent : AlgebraicIndependent ℂ (coordinateRoot p) := by
  have hi : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  have h := (algebraicIndependent_X (Fin 2) ℂ).map
    (f := IsScalarTower.toAlgHom ℂ R (L p)) hi.injOn
  apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions h
  intro i
  have hu : coordinateRoot p 0 ∈ Algebra.adjoin ℂ (Set.range (coordinateRoot p)) :=
    Algebra.subset_adjoin (Set.mem_range_self 0)
  have hv : coordinateRoot p 1 ∈ Algebra.adjoin ℂ (Set.range (coordinateRoot p)) :=
    Algebra.subset_adjoin (Set.mem_range_self 1)
  fin_cases i
  · change algebraMap R (L p) (X 0) ∈ _
    rw [← coordinateRoot_zero_pow p]
    exact Subalgebra.pow_mem _ hu _
  · change algebraMap R (L p) (X 1) ∈ _
    have ha : algebraMap R (L p) (X 0) ∈ Algebra.adjoin ℂ (Set.range (coordinateRoot p)) := by
      rw [← coordinateRoot_zero_pow p]
      exact Subalgebra.pow_mem _ hu _
    have hb : algebraMap R (L p) (X 0 - X 1) ∈ Algebra.adjoin ℂ (Set.range (coordinateRoot p)) := by
      change algebraMap R (L p) (lineForm 4) ∈ _
      rw [← root_pow p 4, original_root_one p]
      exact Subalgebra.pow_mem _ (Subalgebra.mul_mem _ hu hv) _
    simpa [map_sub] using Subalgebra.sub_mem _ ha hb

/-- The x-chart of the blowup of the original plane at (0,0).
Its coordinates s,t map to x,(x−y)/x, and the blowdown is x=s,y=s−st. -/
def C := MvPolynomial (Fin 2) ℂ
instance : CommRing C := inferInstanceAs (CommRing (MvPolynomial (Fin 2) ℂ))
instance : Algebra ℂ C := inferInstanceAs (Algebra ℂ (MvPolynomial (Fin 2) ℂ))
instance : IsRegularRing C := inferInstanceAs (IsRegularRing (MvPolynomial (Fin 2) ℂ))
instance : Algebra.FiniteType ℂ C := inferInstanceAs (Algebra.FiniteType ℂ (MvPolynomial (Fin 2) ℂ))
def blowdown : R →ₐ[ℂ] C := MvPolynomial.aeval ![X 0, X 0 - X 0 * X 1]
instance : Algebra R C := blowdown.toRingHom.toAlgebra
instance : IsScalarTower ℂ R C :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap blowdown).symm

def chartMap : C →ₐ[ℂ] L p := MvPolynomial.aeval ![
  algebraMap R (L p) (X 0), algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)]
instance : Algebra C (L p) := (chartMap p).toRingHom.toAlgebra
instance : IsScalarTower ℂ C (L p) :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap (chartMap p)).symm
lemma chartMap_blowdown : (chartMap p).comp blowdown = IsScalarTower.toAlgHom ℂ R (L p) := by
  apply MvPolynomial.algHom_ext
  intro i
  have hb : blowdown (X i) = ![(X 0 : C), X 0 - X 0 * X 1] i := by
    simp only [blowdown]
    exact MvPolynomial.aeval_X (R := ℂ) (S₁ := C) _ i
  have hc (j : Fin 2) : (chartMap p) (X j) =
      ![algebraMap R (L p) (X 0),
        algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)] j :=
    MvPolynomial.aeval_X (R := ℂ) (S₁ := L p) _ j
  refine (congrArg (chartMap p) hb).trans ?_
  fin_cases i
  · exact hc 0
  · refine (map_sub (chartMap p) (X 0 : C) ((X 0 : C) * (X 1 : C))).trans ?_
    refine (congrArg₂ (fun x y : L p => x - y) (hc 0)
      ((map_mul (chartMap p) (X 0 : C) (X 1 : C)).trans
        (congrArg₂ (fun x y : L p => x * y) (hc 0) (hc 1)))).trans ?_
    change algebraMap R (L p) (X 0) - algebraMap R (L p) (X 0) *
      (algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)) =
      algebraMap R (L p) (X 1)
    have hx : algebraMap R (L p) (X 0) ≠ 0 := by
      change algebraMap R (L p) (lineForm 0) ≠ 0
      rw [← root_pow p 0]
      exact pow_ne_zero _ (root_ne_zero p 0)
    rw [mul_div_cancel₀ _ hx, map_sub, sub_sub_cancel]
instance : IsScalarTower R C (L p) :=
  IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom (chartMap_blowdown p).symm)

lemma chartMap_injective : Function.Injective (chartMap p) := by
  have hi : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  have h := (algebraicIndependent_X (Fin 2) ℂ).map
    (f := IsScalarTower.toAlgHom ℂ R (L p)) hi.injOn
  have hc : AlgebraicIndependent ℂ ![algebraMap R (L p) (X 0),
      algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)] := by
    apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions h
    intro i
    have hs : algebraMap R (L p) (X 0) ∈ Algebra.adjoin ℂ
        (Set.range ![algebraMap R (L p) (X 0),
          algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)]) :=
      Algebra.subset_adjoin ⟨0, rfl⟩
    have ht : algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0) ∈
        Algebra.adjoin ℂ (Set.range ![algebraMap R (L p) (X 0),
          algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)]) :=
      Algebra.subset_adjoin ⟨1, rfl⟩
    fin_cases i
    · exact hs
    · have hx : algebraMap R (L p) (X 0) ≠ 0 := by
        change algebraMap R (L p) (lineForm 0) ≠ 0
        rw [← root_pow p 0]
        exact pow_ne_zero _ (root_ne_zero p 0)
      change algebraMap R (L p) (X 1) ∈ _
      simpa [mul_div_cancel₀ _ hx, map_sub] using Subalgebra.sub_mem _ hs (Subalgebra.mul_mem _ hs ht)
  exact hc

/-- The two ramified coordinates form an actual polynomial plane in the
original field. No independent auxiliary Kummer field is substituted. -/
def coordinateAlgebra : Subalgebra ℂ (L p) :=
  Algebra.adjoin ℂ (Set.range (coordinateRoot p))
abbrev B := coordinateAlgebra p
def planeEquiv : C ≃ₐ[ℂ] B p := (coordinateRoot_independent p).aevalEquiv
instance : IsRegularRing (B p) :=
  IsRegularRing.of_ringEquiv (planeEquiv p).toRingEquiv
instance : IsIntegrallyClosed (B p) := by
  have hC : IsIntegrallyClosed C :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed (A := MvPolynomial (Fin 2) ℂ)
  exact IsIntegrallyClosed.of_equiv (R := C) (S := B p) (planeEquiv p).toRingEquiv

def bRoot (i : Fin 2) : B p :=
  ⟨coordinateRoot p i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
def planeMap : C →ₐ[ℂ] B p := MvPolynomial.aeval ![bRoot p 0 ^ p, bRoot p 1 ^ p]
lemma planeMap_comp : (coordinateAlgebra p).val.comp (planeMap p) = chartMap p := by
  apply MvPolynomial.algHom_ext
  intro i
  change (coordinateAlgebra p).val (MvPolynomial.aeval ![bRoot p 0 ^ p, bRoot p 1 ^ p] (X i)) = _
  simp only [chartMap, MvPolynomial.aeval_X]
  fin_cases i
  · exact coordinateRoot_zero_pow p
  · exact coordinateRoot_one_pow p
instance : Algebra C (B p) := (planeMap p).toRingHom.toAlgebra
instance : IsScalarTower ℂ C (B p) :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap (planeMap p)).symm
instance : IsScalarTower C (B p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom (planeMap_comp p).symm)

lemma coordinateRoot_pow (i : Fin 2) :
    coordinateRoot p i ^ p = algebraMap C (L p) (X i) := by
  change coordinateRoot p i ^ p = MvPolynomial.aeval _ (X i)
  rw [MvPolynomial.aeval_X]
  fin_cases i
  · exact coordinateRoot_zero_pow p
  · exact coordinateRoot_one_pow p
lemma coordinateRoot_integral (i : Fin 2) : IsIntegral C (coordinateRoot p i) := by
  refine ⟨(Polynomial.X : Polynomial C) ^ p - Polynomial.C (R := C) (X i),
    Polynomial.monic_X_pow_sub_C _ (NeZero.ne p), ?_⟩
  change Polynomial.aeval (coordinateRoot p i) _ = 0
  erw [map_sub, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C (R := C) (A := L p)]
  exact sub_eq_zero.mpr (coordinateRoot_pow p i)
instance : Algebra.IsIntegral C (B p) := by
  have hB : coordinateAlgebra p ≤ (integralClosure C (L p)).restrictScalars ℂ := by
    apply Algebra.adjoin_le
    rintro z ⟨i, rfl⟩
    exact coordinateRoot_integral p i
  constructor
  intro b
  have hi : IsIntegral C (b : L p) := hB b.property
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom C (B p) (L p))
    Subtype.val_injective).mp hi
instance : Algebra.FiniteType ℂ (B p) :=
  Algebra.FiniteType.of_surjective (planeEquiv p).toAlgHom (planeEquiv p).surjective
instance : Algebra.FiniteType C (B p) := Algebra.FiniteType.of_restrictScalars_finiteType ℂ C (B p)
instance : Module.Finite C (B p) := Algebra.IsIntegral.finite
end KummerTripleDiagonal

end


noncomputable section
open Algebra MvPolynomial
open nonZeroDivisors
namespace KummerTripleDiagonal
open KummerLines
variable (p : ℕ) [Fact p.Prime]

/-- The actual blowup chart open containing s=t=0 (the intersection of
its exceptional divisor with the strict transform of x−y=0). -/
def cX (i : Fin 2) : C := X i
def chartDenominator : C := (cX 0 - 1) * (cX 0 - cX 0 * cX 1 - 1) * (1 - cX 1)
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

def remainingRoot : Fin 3 → L p := ![root p 2, root p 3, root p 1 / root p 0]
def remainingForm : Fin 3 → C := ![cX 0 - 1, cX 0 - cX 0 * cX 1 - 1, 1 - cX 1]
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
      algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)] i := by
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
  · change root p 3 ^ p = chartMap p (cX 0 - cX 0 * cX 1 - 1)
    rw [root_pow, map_sub, map_one, map_sub, map_mul]
    rw [chartMap_X, chartMap_X]
    change algebraMap R (L p) (X 1 - 1) = algebraMap R (L p) (X 0) -
      algebraMap R (L p) (X 0) *
      (algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)) - 1
    rw [map_sub, map_one]
    have hx : algebraMap R (L p) (X 0) ≠ 0 := by
      change algebraMap R (L p) (lineForm 0) ≠ 0
      rw [← root_pow p 0]
      exact pow_ne_zero _ (root_ne_zero p 0)
    rw [mul_div_cancel₀ _ hx, map_sub, sub_sub_cancel]
  · change (root p 1 / root p 0) ^ p = chartMap p (1 - cX 1)
    rw [div_pow, root_pow, root_pow, map_sub, map_one]
    rw [chartMap_X]
    change algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0) =
      1 - algebraMap R (L p) (X 0 - X 1) / algebraMap R (L p) (X 0)
    rw [map_sub, sub_div]
    have hx : algebraMap R (L p) (X 0) ≠ 0 := by
      change algebraMap R (L p) (lineForm 0) ≠ 0
      rw [← root_pow p 0]
      exact pow_ne_zero _ (root_ne_zero p 0)
    rw [div_self hx, sub_sub_cancel]
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
end KummerTripleDiagonal

end


noncomputable section
open Algebra MvPolynomial
open nonZeroDivisors
namespace KummerTripleDiagonal
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
    have he : root p 1 = coordinateRoot p 0 * remainingRoot p 2 := by
      change root p 1 = root p 0 * (root p 1 / root p 0)
      exact (mul_div_cancel₀ _ (root_ne_zero p 0)).symm
    rw [he]
    exact Subalgebra.mul_mem _ (coordinateRoot_mem_chartRootAlgebra p 0)
      (remainingRoot_mem_chartRootAlgebra p 2)
  · exact remainingRoot_mem_chartRootAlgebra p 0
  · exact remainingRoot_mem_chartRootAlgebra p 1
  · change root p 4 ∈ chartRootAlgebra p
    rw [original_root_one p]
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
end KummerTripleDiagonal


end


noncomputable section
open Algebra MvPolynomial
namespace KummerTripleDiagonal
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
end KummerTripleDiagonal

namespace ExplicitCone

def diagonalSectionDenominator : sectionChart :=
  ⟨y 2 * y 3 * ratioQ, sectionChart.mul_mem
    (sectionChart.mul_mem (y_mem_sectionChart 2) (y_mem_sectionChart 3)) ratioQ_mem_sectionChart⟩
lemma diagonalSectionDenominator_ne_zero : diagonalSectionDenominator ≠ 0 := by
  intro h
  exact mul_ne_zero (mul_ne_zero (y_ne_zero 2) (y_ne_zero 3)) ratioQ_ne_zero
    (congrArg Subtype.val h)
def diagonalSectionOpen : Subalgebra ℂ L :=
  FieldPrincipalOpen.away sectionChart diagonalSectionDenominator diagonalSectionDenominator_ne_zero

def diagonalRegularAlgebra : Subalgebra ℂ L where
  toSubsemiring := (KummerTripleDiagonal.chartRootAlgebra 7).toSubsemiring
  algebraMap_mem' c := by
    have h := (KummerTripleDiagonal.chartRootAlgebra 7).algebraMap_mem
      (algebraMap (KummerTripleDiagonal.B 7) (KummerTripleDiagonal.S 7)
        (algebraMap ℂ (KummerTripleDiagonal.B 7) c))
    rw [← IsScalarTower.algebraMap_apply (KummerTripleDiagonal.B 7) (KummerTripleDiagonal.S 7) L] at h
    exact h

lemma y_mem_diagonalRegular (i : Fin 5) : y i ∈ diagonalRegularAlgebra :=
  KummerTripleDiagonal.allRoots_mem_chartRootAlgebra 7 i
lemma unitRoot_inv_mem_diagonalRegular (i : Fin 3) :
    (KummerTripleDiagonal.remainingRoot 7 i)⁻¹ ∈ diagonalRegularAlgebra :=
  KummerTripleDiagonal.remainingRoot_inv_mem 7 i

lemma ratioQ_mem_diagonalRegular : ratioQ ∈ diagonalRegularAlgebra := by
  have h0 : y 1 / y 0 ∈ diagonalRegularAlgebra :=
    KummerTripleDiagonal.remainingRoot_mem_chartRootAlgebra 7 2
  have h1 : (y 3)⁻¹ ∈ diagonalRegularAlgebra := unitRoot_inv_mem_diagonalRegular 1
  have he : ratioQ = (y 1 / y 0) * y 2 * (y 3)⁻¹ := by
    unfold ratioQ
    field_simp [y_ne_zero]
  rw [he]
  exact diagonalRegularAlgebra.mul_mem
    (diagonalRegularAlgebra.mul_mem h0 (y_mem_diagonalRegular 2)) h1
lemma ratioR_mem_diagonalRegular : ratioR ∈ diagonalRegularAlgebra := by
  have h0 : y 4 / y 0 ∈ diagonalRegularAlgebra :=
    KummerTripleDiagonal.coordinateRoot_mem_chartRootAlgebra 7 1
  have h1 : (y 3)⁻¹ ∈ diagonalRegularAlgebra := unitRoot_inv_mem_diagonalRegular 1
  have he : ratioR = (y 4 / y 0) * (y 3)⁻¹ := by
    unfold ratioR
    field_simp [y_ne_zero]
  rw [he]
  exact diagonalRegularAlgebra.mul_mem h0 h1
lemma sectionChart_le_diagonalRegular : sectionChart ≤ diagonalRegularAlgebra := by
  rw [sectionChart_eq]
  apply Algebra.adjoin_le
  rintro t (⟨i,rfl⟩ | ht)
  · exact y_mem_diagonalRegular i
  · rcases (show t = ratioQ ∨ t = ratioR from by simpa using ht) with rfl | rfl
    · exact ratioQ_mem_diagonalRegular
    · exact ratioR_mem_diagonalRegular
lemma ratioQ_inv_mem_diagonalRegular : ratioQ⁻¹ ∈ diagonalRegularAlgebra := by
  have h0 : (y 1 / y 0)⁻¹ ∈ diagonalRegularAlgebra := unitRoot_inv_mem_diagonalRegular 2
  have h1 : (y 2)⁻¹ ∈ diagonalRegularAlgebra := unitRoot_inv_mem_diagonalRegular 0
  have he : ratioQ⁻¹ = (y 1 / y 0)⁻¹ * y 3 * (y 2)⁻¹ := by
    unfold ratioQ
    field_simp [y_ne_zero]
  rw [he]
  exact diagonalRegularAlgebra.mul_mem
    (diagonalRegularAlgebra.mul_mem h0 (y_mem_diagonalRegular 3)) h1
lemma diagonalSectionOpen_le : diagonalSectionOpen ≤ diagonalRegularAlgebra := by
  apply (FieldPrincipalOpen.away_le_iff sectionChart diagonalSectionDenominator
    diagonalSectionDenominator_ne_zero diagonalRegularAlgebra).mpr
  refine ⟨sectionChart_le_diagonalRegular, ?_⟩
  change (y 2 * y 3 * ratioQ)⁻¹ ∈ diagonalRegularAlgebra
  rw [mul_inv_rev, mul_inv_rev]
  exact diagonalRegularAlgebra.mul_mem ratioQ_inv_mem_diagonalRegular
    (diagonalRegularAlgebra.mul_mem (unitRoot_inv_mem_diagonalRegular 1)
      (unitRoot_inv_mem_diagonalRegular 0))

lemma sectionChart_le_diagonalOpen : sectionChart ≤ diagonalSectionOpen :=
  FieldPrincipalOpen.le_away sectionChart diagonalSectionDenominator diagonalSectionDenominator_ne_zero
lemma y_mem_diagonalOpen (i : Fin 5) : y i ∈ diagonalSectionOpen :=
  sectionChart_le_diagonalOpen (y_mem_sectionChart i)
lemma ratioQ_mem_diagonalOpen : ratioQ ∈ diagonalSectionOpen :=
  sectionChart_le_diagonalOpen ratioQ_mem_sectionChart
lemma ratioR_mem_diagonalOpen : ratioR ∈ diagonalSectionOpen :=
  sectionChart_le_diagonalOpen ratioR_mem_sectionChart
lemma diagonalProduct_inv_mem : (y 2 * y 3 * ratioQ)⁻¹ ∈ diagonalSectionOpen :=
  FieldPrincipalOpen.inv_mem_away sectionChart diagonalSectionDenominator diagonalSectionDenominator_ne_zero
lemma y2_inv_mem_diagonalOpen : (y 2)⁻¹ ∈ diagonalSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem diagonalSectionOpen
    (mul_ne_zero (y_ne_zero 3) ratioQ_ne_zero)
    (diagonalSectionOpen.mul_mem (y_mem_diagonalOpen 3) ratioQ_mem_diagonalOpen)
  simpa only [mul_assoc] using diagonalProduct_inv_mem
lemma y3_inv_mem_diagonalOpen : (y 3)⁻¹ ∈ diagonalSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem diagonalSectionOpen
    (mul_ne_zero (y_ne_zero 2) ratioQ_ne_zero)
    (diagonalSectionOpen.mul_mem (y_mem_diagonalOpen 2) ratioQ_mem_diagonalOpen)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using diagonalProduct_inv_mem
lemma ratioQ_inv_mem_diagonalOpen : ratioQ⁻¹ ∈ diagonalSectionOpen := by
  apply FieldPrincipalOpen.inv_left_mem diagonalSectionOpen
    (mul_ne_zero (y_ne_zero 2) (y_ne_zero 3))
    (diagonalSectionOpen.mul_mem (y_mem_diagonalOpen 2) (y_mem_diagonalOpen 3))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using diagonalProduct_inv_mem

lemma coordinateRoot_mem_diagonalOpen (i : Fin 2) :
    KummerTripleDiagonal.coordinateRoot 7 i ∈ diagonalSectionOpen := by
  fin_cases i
  · exact y_mem_diagonalOpen 0
  · change y 4 / y 0 ∈ diagonalSectionOpen
    have he : y 4 / y 0 = ratioR * y 3 := by
      unfold ratioR
      field_simp [y_ne_zero]
    rw [he]
    exact diagonalSectionOpen.mul_mem ratioR_mem_diagonalOpen (y_mem_diagonalOpen 3)
lemma B_mem_diagonalOpen (b : KummerTripleDiagonal.B 7) : (b : L) ∈ diagonalSectionOpen := by
  have h := b.property
  change (b : L) ∈ Algebra.adjoin ℂ (Set.range (KummerTripleDiagonal.coordinateRoot 7)) at h
  exact (Algebra.adjoin_le (by rintro _ ⟨i,rfl⟩; exact coordinateRoot_mem_diagonalOpen i)) h
lemma remainingRoot_mem_diagonalOpen (i : Fin 3) :
    KummerTripleDiagonal.remainingRoot 7 i ∈ diagonalSectionOpen := by
  fin_cases i
  · exact y_mem_diagonalOpen 2
  · exact y_mem_diagonalOpen 3
  · change y 1 / y 0 ∈ diagonalSectionOpen
    have he : y 1 / y 0 = ratioQ * y 3 * (y 2)⁻¹ := by
      unfold ratioQ
      field_simp [y_ne_zero]
    rw [he]
    exact diagonalSectionOpen.mul_mem
      (diagonalSectionOpen.mul_mem ratioQ_mem_diagonalOpen (y_mem_diagonalOpen 3))
      y2_inv_mem_diagonalOpen
lemma remainingRoot_inv_mem_diagonalOpen (i : Fin 3) :
    (KummerTripleDiagonal.remainingRoot 7 i)⁻¹ ∈ diagonalSectionOpen := by
  fin_cases i
  · exact y2_inv_mem_diagonalOpen
  · exact y3_inv_mem_diagonalOpen
  · change (y 1 / y 0)⁻¹ ∈ diagonalSectionOpen
    have he : (y 1 / y 0)⁻¹ = ratioQ⁻¹ * (y 3)⁻¹ * y 2 := by
      unfold ratioQ
      field_simp [y_ne_zero]
    rw [he]
    exact diagonalSectionOpen.mul_mem
      (diagonalSectionOpen.mul_mem ratioQ_inv_mem_diagonalOpen y3_inv_mem_diagonalOpen)
      (y_mem_diagonalOpen 2)

lemma diagonal_bDenominator_image :
    algebraMap (KummerTripleDiagonal.B 7) L (KummerTripleDiagonal.bDenominator 7) =
    KummerTripleDiagonal.remainingRoot 7 0 ^ 7 * KummerTripleDiagonal.remainingRoot 7 1 ^ 7 *
      KummerTripleDiagonal.remainingRoot 7 2 ^ 7 := by
  change algebraMap (KummerTripleDiagonal.B 7) L
    (algebraMap KummerTripleDiagonal.C (KummerTripleDiagonal.B 7) KummerTripleDiagonal.chartDenominator) = _
  rw [← IsScalarTower.algebraMap_apply KummerTripleDiagonal.C (KummerTripleDiagonal.B 7) L]
  change algebraMap KummerTripleDiagonal.C L
    (KummerTripleDiagonal.remainingForm 0 * KummerTripleDiagonal.remainingForm 1 * KummerTripleDiagonal.remainingForm 2) = _
  simp only [map_mul, KummerTripleDiagonal.remainingRoot_pow]
lemma bDenominator_inv_mem_diagonalOpen :
    (algebraMap (KummerTripleDiagonal.B 7) L (KummerTripleDiagonal.bDenominator 7))⁻¹ ∈ diagonalSectionOpen := by
  rw [diagonal_bDenominator_image, mul_inv_rev, mul_inv_rev, ← inv_pow, ← inv_pow, ← inv_pow]
  exact diagonalSectionOpen.mul_mem (diagonalSectionOpen.pow_mem (remainingRoot_inv_mem_diagonalOpen 2) 7)
    (diagonalSectionOpen.mul_mem (diagonalSectionOpen.pow_mem (remainingRoot_inv_mem_diagonalOpen 1) 7)
      (diagonalSectionOpen.pow_mem (remainingRoot_inv_mem_diagonalOpen 0) 7))
lemma S_mem_diagonalOpen (s : KummerTripleDiagonal.S 7) :
    algebraMap (KummerTripleDiagonal.S 7) L s ∈ diagonalSectionOpen := by
  apply FieldPrincipalOpen.localizationImage_mem diagonalSectionOpen (KummerTripleDiagonal.bDenominator 7)
    ((isUnit_iff_ne_zero).mp (KummerTripleDiagonal.bDenominator_unit_in_L 7))
    (fun b => B_mem_diagonalOpen b) bDenominator_inv_mem_diagonalOpen
lemma diagonalRegular_le_sectionOpen : diagonalRegularAlgebra ≤ diagonalSectionOpen := by
  intro t ht
  change t ∈ Algebra.adjoin (KummerTripleDiagonal.S 7) (KummerTripleDiagonal.remainingRoots 7 : Set L) at ht
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    classical
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image _ from hx)
    exact remainingRoot_mem_diagonalOpen i
  | algebraMap s => exact S_mem_diagonalOpen s
  | add x y hx hy h₁ h₂ => exact diagonalSectionOpen.add_mem h₁ h₂
  | mul x y hx hy h₁ h₂ => exact diagonalSectionOpen.mul_mem h₁ h₂

/-- The literal polarization chart, localized at c*d*q, is exactly the
regular normalization of the literal diagonal-point blowup open, within the
same original function field. -/
theorem diagonalSectionOpen_eq : diagonalSectionOpen = diagonalRegularAlgebra :=
  le_antisymm diagonalSectionOpen_le diagonalRegular_le_sectionOpen

theorem sectionChart_diagonalOpen_regular :
    IsRegularRing (Localization.Away diagonalSectionDenominator) := by
  have : IsRegularRing diagonalRegularAlgebra := KummerTripleDiagonal.chartRootAlgebra_regular 7
  exact FieldPrincipalOpen.regular_away_of_eq sectionChart diagonalSectionDenominator
    diagonalSectionDenominator_ne_zero diagonalRegularAlgebra diagonalSectionOpen_eq

end ExplicitCone

end


noncomputable section
open Algebra MvPolynomial
namespace KummerShifted
open KummerLines
variable (p : ℕ) [Fact p.Prime]
local instance : IsScalarTower ℂ R (L p) := IsScalarTower.of_algebraMap_eq' rfl
abbrev root := KummerTriple.root
lemma root_pow (i : Fin 5) : root p i ^ p = algebraMap R (L p) (lineForm i) :=
  KummerTriple.root_pow p i
lemma root_ne_zero (i : Fin 5) : root p i ≠ 0 := KummerTriple.root_ne_zero p i

/-- Literal y-chart over the other affine triple point (1,1). -/
def coordinateRoot : Fin 2 → L p := ![root p 3, root p 2 / root p 3]
lemma coordinateRoot_zero_pow : coordinateRoot p 0 ^ p = algebraMap R (L p) (X 1 - 1) :=
  root_pow p 3
lemma coordinateRoot_one_pow : coordinateRoot p 1 ^ p =
    algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1) := by
  change (root p 2 / root p 3) ^ p = _
  rw [div_pow, root_pow, root_pow]
  rfl
lemma original_root_two : root p 2 = coordinateRoot p 0 * coordinateRoot p 1 := by
  change root p 2 = root p 3 * (root p 2 / root p 3)
  field_simp [root_ne_zero p 3]
lemma original_x : algebraMap R (L p) (X 0) =
    (coordinateRoot p 0 * coordinateRoot p 1) ^ p + 1 := by
  rw [← original_root_two p, root_pow]
  change algebraMap R (L p) (X 0) = algebraMap R (L p) (X 0 - 1) + 1
  rw [map_sub, map_one, sub_add_cancel]
lemma original_y : algebraMap R (L p) (X 1) = coordinateRoot p 0 ^ p + 1 := by
  rw [coordinateRoot_zero_pow, map_sub, map_one, sub_add_cancel]
lemma coordinateRoot_independent : AlgebraicIndependent ℂ (coordinateRoot p) := by
  have hi : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  have h := (algebraicIndependent_X (Fin 2) ℂ).map
    (f := IsScalarTower.toAlgHom ℂ R (L p)) hi.injOn
  apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions h
  intro i
  have hu : coordinateRoot p 0 ∈ Algebra.adjoin ℂ (Set.range (coordinateRoot p)) :=
    Algebra.subset_adjoin (Set.mem_range_self 0)
  have hv : coordinateRoot p 1 ∈ Algebra.adjoin ℂ (Set.range (coordinateRoot p)) :=
    Algebra.subset_adjoin (Set.mem_range_self 1)
  fin_cases i
  · change algebraMap R (L p) (X 0) ∈ _
    rw [original_x p]
    exact Subalgebra.add_mem _ (Subalgebra.pow_mem _ (Subalgebra.mul_mem _ hu hv) _) (one_mem _)
  · change algebraMap R (L p) (X 1) ∈ _
    rw [original_y p]
    exact Subalgebra.add_mem _ (Subalgebra.pow_mem _ hu _) (one_mem _)

def C := MvPolynomial (Fin 2) ℂ
instance : CommRing C := inferInstanceAs (CommRing (MvPolynomial (Fin 2) ℂ))
instance : Algebra ℂ C := inferInstanceAs (Algebra ℂ (MvPolynomial (Fin 2) ℂ))
instance : IsRegularRing C := inferInstanceAs (IsRegularRing (MvPolynomial (Fin 2) ℂ))
instance : Algebra.FiniteType ℂ C := inferInstanceAs (Algebra.FiniteType ℂ (MvPolynomial (Fin 2) ℂ))
def blowdown : R →ₐ[ℂ] C := MvPolynomial.aeval ![X 0 * X 1 + 1, X 0 + 1]
instance : Algebra R C := blowdown.toRingHom.toAlgebra
instance : IsScalarTower ℂ R C :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap blowdown).symm

def chartMap : C →ₐ[ℂ] L p := MvPolynomial.aeval ![
  algebraMap R (L p) (X 1 - 1),
  algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1)]
instance : Algebra C (L p) := (chartMap p).toRingHom.toAlgebra
instance : IsScalarTower ℂ C (L p) :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap (chartMap p)).symm
lemma chartMap_blowdown : (chartMap p).comp blowdown = IsScalarTower.toAlgHom ℂ R (L p) := by
  have hd : algebraMap R (L p) (X 1 - 1) ≠ 0 := by
    rw [← coordinateRoot_zero_pow p]
    exact pow_ne_zero _ (root_ne_zero p 3)
  apply MvPolynomial.algHom_ext
  intro i
  have hb : blowdown (X i) = ![(X 0 : C) * X 1 + 1, X 0 + 1] i := by
    simp only [blowdown]
    exact MvPolynomial.aeval_X (R := ℂ) (S₁ := C) _ i
  have hc (j : Fin 2) : (chartMap p) (X j) =
      ![algebraMap R (L p) (X 1 - 1),
        algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1)] j :=
    MvPolynomial.aeval_X (R := ℂ) (S₁ := L p) _ j
  refine (congrArg (chartMap p) hb).trans ?_
  fin_cases i
  · refine (map_add (chartMap p) ((X 0 : C) * (X 1 : C)) (1 : C)).trans ?_
    refine (congrArg₂ (fun x y : L p => x + y)
      ((map_mul (chartMap p) (X 0 : C) (X 1 : C)).trans
        (congrArg₂ (fun x y : L p => x * y) (hc 0) (hc 1)))
      (map_one (chartMap p))).trans ?_
    change algebraMap R (L p) (X 1 - 1) *
      (algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1)) + 1 = _
    rw [mul_div_cancel₀ _ hd, map_sub, map_one, sub_add_cancel]
    rfl
  · refine (map_add (chartMap p) (X 0 : C) (1 : C)).trans ?_
    refine (congrArg₂ (fun x y : L p => x + y) (hc 0) (map_one (chartMap p))).trans ?_
    change algebraMap R (L p) (X 1 - 1) + 1 = _
    rw [map_sub, map_one, sub_add_cancel]
    rfl
instance : IsScalarTower R C (L p) :=
  IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom (chartMap_blowdown p).symm)

lemma chartMap_injective : Function.Injective (chartMap p) := by
  have hi : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  have h := (algebraicIndependent_X (Fin 2) ℂ).map
    (f := IsScalarTower.toAlgHom ℂ R (L p)) hi.injOn
  have hc : AlgebraicIndependent ℂ ![algebraMap R (L p) (X 1 - 1),
      algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1)] := by
    apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions h
    intro i
    have hs : algebraMap R (L p) (X 1 - 1) ∈ Algebra.adjoin ℂ
        (Set.range ![algebraMap R (L p) (X 1 - 1),
          algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1)]) :=
      Algebra.subset_adjoin ⟨0, rfl⟩
    have ht : algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1) ∈
        Algebra.adjoin ℂ (Set.range ![algebraMap R (L p) (X 1 - 1),
          algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1)]) :=
      Algebra.subset_adjoin ⟨1, rfl⟩
    have hd : algebraMap R (L p) (X 1 - 1) ≠ 0 := by
      rw [← coordinateRoot_zero_pow p]
      exact pow_ne_zero _ (root_ne_zero p 3)
    fin_cases i
    · change algebraMap R (L p) (X 0) ∈ _
      have hx : algebraMap R (L p) (X 0) =
          algebraMap R (L p) (X 1 - 1) *
            (algebraMap R (L p) (X 0 - 1) / algebraMap R (L p) (X 1 - 1)) + 1 := by
        rw [mul_div_cancel₀ _ hd, map_sub, map_one, sub_add_cancel]
      rw [hx]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hs ht) (one_mem _)
    · change algebraMap R (L p) (X 1) ∈ _
      have hy : algebraMap R (L p) (X 1) = algebraMap R (L p) (X 1 - 1) + 1 := by
        rw [map_sub, map_one, sub_add_cancel]
      rw [hy]
      exact Subalgebra.add_mem _ hs (one_mem _)
  exact hc

/-- The two ramified coordinates form an actual polynomial plane in the
original field. No independent auxiliary Kummer field is substituted. -/
def coordinateAlgebra : Subalgebra ℂ (L p) :=
  Algebra.adjoin ℂ (Set.range (coordinateRoot p))
abbrev B := coordinateAlgebra p
def planeEquiv : C ≃ₐ[ℂ] B p := (coordinateRoot_independent p).aevalEquiv
instance : IsRegularRing (B p) :=
  IsRegularRing.of_ringEquiv (planeEquiv p).toRingEquiv
instance : IsIntegrallyClosed (B p) := by
  have hC : IsIntegrallyClosed C :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed (A := MvPolynomial (Fin 2) ℂ)
  exact IsIntegrallyClosed.of_equiv (R := C) (S := B p) (planeEquiv p).toRingEquiv

def bRoot (i : Fin 2) : B p :=
  ⟨coordinateRoot p i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
def planeMap : C →ₐ[ℂ] B p := MvPolynomial.aeval ![bRoot p 0 ^ p, bRoot p 1 ^ p]
lemma planeMap_comp : (coordinateAlgebra p).val.comp (planeMap p) = chartMap p := by
  apply MvPolynomial.algHom_ext
  intro i
  change (coordinateAlgebra p).val (MvPolynomial.aeval ![bRoot p 0 ^ p, bRoot p 1 ^ p] (X i)) = _
  simp only [chartMap, MvPolynomial.aeval_X]
  fin_cases i
  · exact coordinateRoot_zero_pow p
  · exact coordinateRoot_one_pow p
instance : Algebra C (B p) := (planeMap p).toRingHom.toAlgebra
instance : IsScalarTower ℂ C (B p) :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap (planeMap p)).symm
instance : IsScalarTower C (B p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom (planeMap_comp p).symm)

lemma coordinateRoot_pow (i : Fin 2) :
    coordinateRoot p i ^ p = algebraMap C (L p) (X i) := by
  change coordinateRoot p i ^ p = MvPolynomial.aeval _ (X i)
  rw [MvPolynomial.aeval_X]
  fin_cases i
  · exact coordinateRoot_zero_pow p
  · exact coordinateRoot_one_pow p
lemma coordinateRoot_integral (i : Fin 2) : IsIntegral C (coordinateRoot p i) := by
  refine ⟨(Polynomial.X : Polynomial C) ^ p - Polynomial.C (R := C) (X i),
    Polynomial.monic_X_pow_sub_C _ (NeZero.ne p), ?_⟩
  change Polynomial.aeval (coordinateRoot p i) _ = 0
  erw [map_sub, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C (R := C) (A := L p)]
  exact sub_eq_zero.mpr (coordinateRoot_pow p i)
instance : Algebra.IsIntegral C (B p) := by
  have hB : coordinateAlgebra p ≤ (integralClosure C (L p)).restrictScalars ℂ := by
    apply Algebra.adjoin_le
    rintro z ⟨i, rfl⟩
    exact coordinateRoot_integral p i
  constructor
  intro b
  have hi : IsIntegral C (b : L p) := hB b.property
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom C (B p) (L p))
    Subtype.val_injective).mp hi
instance : Algebra.FiniteType ℂ (B p) :=
  Algebra.FiniteType.of_surjective (planeEquiv p).toAlgHom (planeEquiv p).surjective
instance : Algebra.FiniteType C (B p) := Algebra.FiniteType.of_restrictScalars_finiteType ℂ C (B p)
instance : Module.Finite C (B p) := Algebra.IsIntegral.finite
end KummerShifted

end

end OAI
