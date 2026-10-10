import OAI.AlgebraicGeometry.SurfaceCones.ExteriorFunctor
import OAI.AlgebraicGeometry.SurfaceCones.KummerShiftedDiagonalNormalization

namespace OAI

/-! Canonical-density frames on the remaining triple-point coordinate charts. -/
noncomputable section
open Algebra Module KaehlerDifferential
namespace CanonicalCoordinates
variable {k A M : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M]

lemma volume_complement (d : Derivation k A M) (x y : A) :
    ExteriorAlgebra.ι A (d x) * ExteriorAlgebra.ι A (d (x-y)) =
      -(ExteriorAlgebra.ι A (d x) * ExteriorAlgebra.ι A (d y)) := by
  simp only [map_sub, mul_sub, ExteriorAlgebra.ι_sq_zero, zero_sub]

lemma coordinateJacobian_diagonal (d : Derivation k A M) (u v : A) :
    ExteriorAlgebra.ι A (d (u^7)) *
      ExteriorAlgebra.ι A (d (u^7-(u*v)^7)) =
    (-49 * u^13 * v^6) •
      (ExteriorAlgebra.ι A (d u) * ExteriorAlgebra.ι A (d v)) := by
  rw [volume_complement, coordinateJacobian_seven]
  rw [← neg_smul]
  congr 1
  ring

lemma coordinateJacobian_shifted (d : Derivation k A M) (u v : A) :
    ExteriorAlgebra.ι A (d ((u*v)^7+1)) *
      ExteriorAlgebra.ι A (d (u^7+1)) =
    (-49 * u^13 * v^6) •
      (ExteriorAlgebra.ι A (d u) * ExteriorAlgebra.ι A (d v)) := by
  simp only [map_add, Derivation.map_one_eq_zero, add_zero]
  rw [volume_swap, coordinateJacobian_seven, ← neg_smul]
  congr 1
  ring

lemma coordinateJacobian_shiftedDiagonal (d : Derivation k A M) (u v : A) :
    ExteriorAlgebra.ι A (d ((u*v)^7+u^7+1)) *
      ExteriorAlgebra.ι A (d (u^7+1)) =
    (-49 * u^13 * v^6) •
      (ExteriorAlgebra.ι A (d u) * ExteriorAlgebra.ι A (d v)) := by
  simp only [map_add, Derivation.map_one_eq_zero, add_zero, add_mul,
    ExteriorAlgebra.ι_sq_zero, add_zero]
  rw [volume_swap, coordinateJacobian_seven, ← neg_smul]
  congr 1
  ring
end CanonicalCoordinates

namespace KummerTripleDiagonal
open KummerLines
variable (p : ℕ) [Fact p.Prime]
local instance canonicalBRootAlgebra : Algebra (B p) (chartRootAlgebra p) :=
  ((algebraMap (S p) (chartRootAlgebra p)).comp (algebraMap (B p) (S p))).toAlgebra
local instance : SMul (B p) (chartRootAlgebra p) :=
  @Algebra.toSMul (B p) (chartRootAlgebra p) _ _ (canonicalBRootAlgebra p)
local instance : Module (B p) (chartRootAlgebra p) :=
  @Algebra.toModule (B p) (chartRootAlgebra p) _ _ (canonicalBRootAlgebra p)
local instance : IsScalarTower (B p) (S p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance canonicalCAlgebra : Algebra ℂ (chartRootAlgebra p) :=
  ((algebraMap (B p) (chartRootAlgebra p)).comp (algebraMap ℂ (B p))).toAlgebra
local instance : SMul ℂ (chartRootAlgebra p) :=
  @Algebra.toSMul ℂ (chartRootAlgebra p) _ _ (canonicalCAlgebra p)
local instance : Module ℂ (chartRootAlgebra p) :=
  @Algebra.toModule ℂ (chartRootAlgebra p) _ _ (canonicalCAlgebra p)
local instance : IsScalarTower ℂ (B p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : Algebra.Etale (S p) (chartRootAlgebra p) :=
  (chartRootAlgebra_finiteFreeEtale p).1
local instance : Algebra.FormallyEtale (B p) (chartRootAlgebra p) :=
  Algebra.FormallyEtale.comp (B p) (S p) (chartRootAlgebra p)

local instance : Module (chartRootAlgebra p) Ω[chartRootAlgebra p⁄ℂ] :=
  CanonicalCoordinates.kaehlerModule ℂ (chartRootAlgebra p)

/-- The smooth normalization has cotangent basis du,dv. -/
def cotangentBasis : Basis (Fin 2) (chartRootAlgebra p) Ω[chartRootAlgebra p⁄ℂ] :=
  CanonicalCoordinates.etaleBasis (k := ℂ) (B := B p)
    (A := chartRootAlgebra p) (planeEquiv p)

def chartCoordinate (i : Fin 2) : chartRootAlgebra p :=
  algebraMap (B p) (chartRootAlgebra p) (bRoot p i)

lemma cotangentBasis_apply (i : Fin 2) :
    cotangentBasis p i = D ℂ (chartRootAlgebra p) (chartCoordinate p i) := by
  erw [cotangentBasis, CanonicalCoordinates.etaleBasis_apply]
  congr 2
  apply Subtype.ext
  exact MvPolynomial.aeval_X (coordinateRoot p) i

def remainingElement (i : Fin 3) : chartRootAlgebra p :=
  ⟨remainingRoot p i, remainingRoot_mem_chartRootAlgebra p i⟩

lemma remainingElement_pow (i : Fin 3) :
    remainingElement p i ^ p =
      algebraMap (S p) (chartRootAlgebra p) (algebraMap C (S p) (remainingForm i)) := by
  apply Subtype.ext
  change remainingRoot p i ^ p =
    algebraMap (S p) (L p) (algebraMap C (S p) (remainingForm i))
  rw [← IsScalarTower.algebraMap_apply C (S p) (L p)]
  exact remainingRoot_pow p i

lemma remainingElement_isUnit (i : Fin 3) : IsUnit (remainingElement p i) := by
  rw [← isUnit_pow_iff (NeZero.ne p), remainingElement_pow]
  exact (remaining_unit p i).map (algebraMap (S p) (chartRootAlgebra p))

def remainingUnit (i : Fin 3) : (chartRootAlgebra p)ˣ :=
  (remainingElement_isUnit p i).unit

@[simp] lemma remainingUnit_val (i : Fin 3) :
    (remainingUnit p i : chartRootAlgebra p) = remainingElement p i :=
  IsUnit.unit_spec _

lemma remainingUnit_to_field (i : Fin 3) :
    algebraMap (chartRootAlgebra p) (L p) (remainingUnit p i : chartRootAlgebra p) =
      remainingRoot p i := by
  rw [remainingUnit_val]
  rfl

local instance : IsScalarTower (B 7) (chartRootAlgebra 7) (L 7) :=
  CanonicalCoordinates.towerViaMiddle (B 7) (S 7) (chartRootAlgebra 7) (L 7)
local instance : IsScalarTower ℂ (chartRootAlgebra 7) (L 7) :=
  CanonicalCoordinates.towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (L 7) Ω[L 7⁄ℂ] := CanonicalCoordinates.kaehlerModule ℂ (L 7)
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorSMul _ _
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorMulAction _ _
local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.topModule _ _
local instance : SMul (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  (CanonicalCoordinates.topModule _ _).toSMul

lemma chartCoordinate_to_field (i : Fin 2) :
    algebraMap (chartRootAlgebra 7) (L 7) (chartCoordinate 7 i) = coordinateRoot 7 i := by
  rw [chartCoordinate, ← IsScalarTower.algebraMap_apply (B 7) (chartRootAlgebra 7) (L 7)]
  rfl

def canonicalUnit : (chartRootAlgebra 7)ˣ :=
  -((exponent_unit 7).map (algebraMap (S 7) (chartRootAlgebra 7))).unit ^ 2 *
    (remainingUnit 7 0 ^ 6 * remainingUnit 7 1 ^ 1 * remainingUnit 7 2 ^ 6)⁻¹

lemma canonicalUnit_to_field :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      -49 / (root 7 2 ^ 6 * root 7 3 ^ 1 * (root 7 1 / root 7 0) ^ 6) := by
  have hneg (a : chartRootAlgebra 7) :
      algebraMap (chartRootAlgebra 7) (L 7) (-a) =
        -algebraMap (chartRootAlgebra 7) (L 7) a :=
    (algebraMap (chartRootAlgebra 7) (L 7)).map_neg a
  simp only [canonicalUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, map_mul, map_pow, hneg, map_units_inv,
    remainingUnit_to_field, IsUnit.unit_spec, map_natCast]
  change -(7 : L 7)^2 * (root 7 2 ^ 6 * root 7 3 ^ 1 * (root 7 1 / root 7 0) ^ 6)⁻¹ = _
  norm_num [div_eq_mul_inv]

lemma canonical_density_identity :
    ExplicitCone.sectionCoefficient (0,0)^5 *
      (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6) /
        (∏ i : Fin 5, root 7 i)^6 =
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) := by
  rw [canonicalUnit_to_field]
  have h0 := root_ne_zero 7 0
  have h1 := root_ne_zero 7 1
  have h2 := root_ne_zero 7 2
  have h3 := root_ne_zero 7 3
  have h4 := root_ne_zero 7 4
  have hc : ExplicitCone.sectionCoefficient (0,0) = root 7 0 * root 7 3 := by
    change (1 : L 7) * root 7 0 * root 7 3 = _
    simp only [one_mul]
  have hp : (∏ i : Fin 5, root 7 i) =
      root 7 0 * root 7 1 * root 7 2 * root 7 3 * root 7 4 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change root 7 0 * (root 7 1 * (root 7 2 * (root 7 3 * root 7 4))) = _
    ring
  rw [hc, hp]
  change (root 7 0 * root 7 3)^5 *
    (-49 * (root 7 0)^13 * (root 7 4 / root 7 0)^6) / _ = _
  field_simp [h0,h1,h2,h3,h4]

def canonicalFrame : Basis Unit (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.unitTopBasis (cotangentBasis 7) canonicalUnit

lemma canonicalFrame_to_field :
    CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
      (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) =
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) •
      (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
        ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1))) := by
  have hf := CanonicalCoordinates.exteriorMap_frame ℂ (chartRootAlgebra 7) (L 7)
    (cotangentBasis 7) canonicalUnit (chartCoordinate 7) (cotangentBasis_apply 7)
  change CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
    (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) = _ at hf
  simpa only [chartCoordinate_to_field] using hf

lemma canonicalForm_eq : KummerTriple.canonicalForm =
    (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
      (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6)) •
      (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
        ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1))) := by
  rw [KummerTriple.canonicalForm, ← coordinateRoot_zero_pow 7]
  have hy : algebraMap R (L 7) (MvPolynomial.X 1) =
      (coordinateRoot 7 0)^7-(coordinateRoot 7 0 * coordinateRoot 7 1)^7 := by
    rw [← original_root_one 7, coordinateRoot_zero_pow, root_pow]
    change _ = algebraMap R (L 7) (MvPolynomial.X 0) -
      algebraMap R (L 7) (MvPolynomial.X 0 - MvPolynomial.X 1)
    rw [map_sub]; ring
  rw [hy, CanonicalCoordinates.coordinateJacobian_diagonal, smul_smul]

lemma canonical_density_scalar :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      ExplicitCone.sectionCoefficient (0,0)^5 *
        (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
          (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6)) := by
  rw [← canonical_density_identity]
  ring

lemma canonicalFrame_rational :
    CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
      (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) =
    ExplicitCone.sectionCoefficient (0,0)^5 • KummerTriple.canonicalForm := by
  rw [canonicalFrame_to_field, canonicalForm_eq, smul_smul]
  exact congrArg (fun a : L 7 => a •
    (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
      ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1)))) canonical_density_scalar

end KummerTripleDiagonal

namespace KummerShifted
open KummerLines
variable (p : ℕ) [Fact p.Prime]
local instance canonicalBRootAlgebra : Algebra (B p) (chartRootAlgebra p) :=
  ((algebraMap (S p) (chartRootAlgebra p)).comp (algebraMap (B p) (S p))).toAlgebra
local instance : SMul (B p) (chartRootAlgebra p) :=
  @Algebra.toSMul (B p) (chartRootAlgebra p) _ _ (canonicalBRootAlgebra p)
local instance : Module (B p) (chartRootAlgebra p) :=
  @Algebra.toModule (B p) (chartRootAlgebra p) _ _ (canonicalBRootAlgebra p)
local instance : IsScalarTower (B p) (S p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance canonicalCAlgebra : Algebra ℂ (chartRootAlgebra p) :=
  ((algebraMap (B p) (chartRootAlgebra p)).comp (algebraMap ℂ (B p))).toAlgebra
local instance : SMul ℂ (chartRootAlgebra p) :=
  @Algebra.toSMul ℂ (chartRootAlgebra p) _ _ (canonicalCAlgebra p)
local instance : Module ℂ (chartRootAlgebra p) :=
  @Algebra.toModule ℂ (chartRootAlgebra p) _ _ (canonicalCAlgebra p)
local instance : IsScalarTower ℂ (B p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : Algebra.Etale (S p) (chartRootAlgebra p) :=
  (chartRootAlgebra_finiteFreeEtale p).1
local instance : Algebra.FormallyEtale (B p) (chartRootAlgebra p) :=
  Algebra.FormallyEtale.comp (B p) (S p) (chartRootAlgebra p)

local instance : Module (chartRootAlgebra p) Ω[chartRootAlgebra p⁄ℂ] :=
  CanonicalCoordinates.kaehlerModule ℂ (chartRootAlgebra p)

/-- The smooth normalization has cotangent basis du,dv. -/
def cotangentBasis : Basis (Fin 2) (chartRootAlgebra p) Ω[chartRootAlgebra p⁄ℂ] :=
  CanonicalCoordinates.etaleBasis (k := ℂ) (B := B p)
    (A := chartRootAlgebra p) (planeEquiv p)

def chartCoordinate (i : Fin 2) : chartRootAlgebra p :=
  algebraMap (B p) (chartRootAlgebra p) (bRoot p i)

lemma cotangentBasis_apply (i : Fin 2) :
    cotangentBasis p i = D ℂ (chartRootAlgebra p) (chartCoordinate p i) := by
  erw [cotangentBasis, CanonicalCoordinates.etaleBasis_apply]
  congr 2
  apply Subtype.ext
  exact MvPolynomial.aeval_X (coordinateRoot p) i

def remainingElement (i : Fin 3) : chartRootAlgebra p :=
  ⟨remainingRoot p i, remainingRoot_mem_chartRootAlgebra p i⟩

lemma remainingElement_pow (i : Fin 3) :
    remainingElement p i ^ p =
      algebraMap (S p) (chartRootAlgebra p) (algebraMap C (S p) (remainingForm i)) := by
  apply Subtype.ext
  change remainingRoot p i ^ p =
    algebraMap (S p) (L p) (algebraMap C (S p) (remainingForm i))
  rw [← IsScalarTower.algebraMap_apply C (S p) (L p)]
  exact remainingRoot_pow p i

lemma remainingElement_isUnit (i : Fin 3) : IsUnit (remainingElement p i) := by
  rw [← isUnit_pow_iff (NeZero.ne p), remainingElement_pow]
  exact (remaining_unit p i).map (algebraMap (S p) (chartRootAlgebra p))

def remainingUnit (i : Fin 3) : (chartRootAlgebra p)ˣ :=
  (remainingElement_isUnit p i).unit

@[simp] lemma remainingUnit_val (i : Fin 3) :
    (remainingUnit p i : chartRootAlgebra p) = remainingElement p i :=
  IsUnit.unit_spec _

lemma remainingUnit_to_field (i : Fin 3) :
    algebraMap (chartRootAlgebra p) (L p) (remainingUnit p i : chartRootAlgebra p) =
      remainingRoot p i := by
  rw [remainingUnit_val]
  rfl

local instance : IsScalarTower (B 7) (chartRootAlgebra 7) (L 7) :=
  CanonicalCoordinates.towerViaMiddle (B 7) (S 7) (chartRootAlgebra 7) (L 7)
local instance : IsScalarTower ℂ (chartRootAlgebra 7) (L 7) :=
  CanonicalCoordinates.towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (L 7) Ω[L 7⁄ℂ] := CanonicalCoordinates.kaehlerModule ℂ (L 7)
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorSMul _ _
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorMulAction _ _
local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.topModule _ _
local instance : SMul (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  (CanonicalCoordinates.topModule _ _).toSMul

lemma chartCoordinate_to_field (i : Fin 2) :
    algebraMap (chartRootAlgebra 7) (L 7) (chartCoordinate 7 i) = coordinateRoot 7 i := by
  rw [chartCoordinate, ← IsScalarTower.algebraMap_apply (B 7) (chartRootAlgebra 7) (L 7)]
  rfl

def canonicalUnit : (chartRootAlgebra 7)ˣ :=
  -((exponent_unit 7).map (algebraMap (S 7) (chartRootAlgebra 7))).unit ^ 2 *
    (remainingUnit 7 0 ^ 1 * remainingUnit 7 1 ^ 6 * remainingUnit 7 2 ^ 6)⁻¹

lemma canonicalUnit_to_field :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      -49 / (root 7 0 ^ 1 * root 7 1 ^ 6 * (root 7 4 / root 7 3) ^ 6) := by
  have hneg (a : chartRootAlgebra 7) :
      algebraMap (chartRootAlgebra 7) (L 7) (-a) =
        -algebraMap (chartRootAlgebra 7) (L 7) a :=
    (algebraMap (chartRootAlgebra 7) (L 7)).map_neg a
  simp only [canonicalUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, map_mul, map_pow, hneg, map_units_inv,
    remainingUnit_to_field, IsUnit.unit_spec, map_natCast]
  change -(7 : L 7)^2 * (root 7 0 ^ 1 * root 7 1 ^ 6 * (root 7 4 / root 7 3) ^ 6)⁻¹ = _
  norm_num [div_eq_mul_inv]

lemma canonical_density_identity :
    ExplicitCone.sectionCoefficient (0,0)^5 *
      (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6) /
        (∏ i : Fin 5, root 7 i)^6 =
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) := by
  rw [canonicalUnit_to_field]
  have h0 := root_ne_zero 7 0
  have h1 := root_ne_zero 7 1
  have h2 := root_ne_zero 7 2
  have h3 := root_ne_zero 7 3
  have h4 := root_ne_zero 7 4
  have hc : ExplicitCone.sectionCoefficient (0,0) = root 7 0 * root 7 3 := by
    change (1 : L 7) * root 7 0 * root 7 3 = _
    simp only [one_mul]
  have hp : (∏ i : Fin 5, root 7 i) =
      root 7 0 * root 7 1 * root 7 2 * root 7 3 * root 7 4 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change root 7 0 * (root 7 1 * (root 7 2 * (root 7 3 * root 7 4))) = _
    ring
  rw [hc, hp]
  change (root 7 0 * root 7 3)^5 *
    (-49 * (root 7 3)^13 * (root 7 2 / root 7 3)^6) / _ = _
  field_simp [h0,h1,h2,h3,h4]

def canonicalFrame : Basis Unit (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.unitTopBasis (cotangentBasis 7) canonicalUnit

lemma canonicalFrame_to_field :
    CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
      (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) =
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) •
      (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
        ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1))) := by
  have hf := CanonicalCoordinates.exteriorMap_frame ℂ (chartRootAlgebra 7) (L 7)
    (cotangentBasis 7) canonicalUnit (chartCoordinate 7) (cotangentBasis_apply 7)
  change CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
    (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) = _ at hf
  simpa only [chartCoordinate_to_field] using hf

lemma canonicalForm_eq : KummerTriple.canonicalForm =
    (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
      (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6)) •
      (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
        ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1))) := by
  rw [KummerTriple.canonicalForm, original_x, original_y,
    CanonicalCoordinates.coordinateJacobian_shifted, smul_smul]

lemma canonical_density_scalar :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      ExplicitCone.sectionCoefficient (0,0)^5 *
        (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
          (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6)) := by
  rw [← canonical_density_identity]
  ring

lemma canonicalFrame_rational :
    CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
      (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) =
    ExplicitCone.sectionCoefficient (0,0)^5 • KummerTriple.canonicalForm := by
  rw [canonicalFrame_to_field, canonicalForm_eq, smul_smul]
  exact congrArg (fun a : L 7 => a •
    (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
      ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1)))) canonical_density_scalar

end KummerShifted

namespace KummerShiftedDiagonal
open KummerLines
variable (p : ℕ) [Fact p.Prime]
local instance canonicalBRootAlgebra : Algebra (B p) (chartRootAlgebra p) :=
  ((algebraMap (S p) (chartRootAlgebra p)).comp (algebraMap (B p) (S p))).toAlgebra
local instance : SMul (B p) (chartRootAlgebra p) :=
  @Algebra.toSMul (B p) (chartRootAlgebra p) _ _ (canonicalBRootAlgebra p)
local instance : Module (B p) (chartRootAlgebra p) :=
  @Algebra.toModule (B p) (chartRootAlgebra p) _ _ (canonicalBRootAlgebra p)
local instance : IsScalarTower (B p) (S p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance canonicalCAlgebra : Algebra ℂ (chartRootAlgebra p) :=
  ((algebraMap (B p) (chartRootAlgebra p)).comp (algebraMap ℂ (B p))).toAlgebra
local instance : SMul ℂ (chartRootAlgebra p) :=
  @Algebra.toSMul ℂ (chartRootAlgebra p) _ _ (canonicalCAlgebra p)
local instance : Module ℂ (chartRootAlgebra p) :=
  @Algebra.toModule ℂ (chartRootAlgebra p) _ _ (canonicalCAlgebra p)
local instance : IsScalarTower ℂ (B p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : Algebra.Etale (S p) (chartRootAlgebra p) :=
  (chartRootAlgebra_finiteFreeEtale p).1
local instance : Algebra.FormallyEtale (B p) (chartRootAlgebra p) :=
  Algebra.FormallyEtale.comp (B p) (S p) (chartRootAlgebra p)

local instance : Module (chartRootAlgebra p) Ω[chartRootAlgebra p⁄ℂ] :=
  CanonicalCoordinates.kaehlerModule ℂ (chartRootAlgebra p)

/-- The smooth normalization has cotangent basis du,dv. -/
def cotangentBasis : Basis (Fin 2) (chartRootAlgebra p) Ω[chartRootAlgebra p⁄ℂ] :=
  CanonicalCoordinates.etaleBasis (k := ℂ) (B := B p)
    (A := chartRootAlgebra p) (planeEquiv p)

def chartCoordinate (i : Fin 2) : chartRootAlgebra p :=
  algebraMap (B p) (chartRootAlgebra p) (bRoot p i)

lemma cotangentBasis_apply (i : Fin 2) :
    cotangentBasis p i = D ℂ (chartRootAlgebra p) (chartCoordinate p i) := by
  erw [cotangentBasis, CanonicalCoordinates.etaleBasis_apply]
  congr 2
  apply Subtype.ext
  exact MvPolynomial.aeval_X (coordinateRoot p) i

def remainingElement (i : Fin 3) : chartRootAlgebra p :=
  ⟨remainingRoot p i, remainingRoot_mem_chartRootAlgebra p i⟩

lemma remainingElement_pow (i : Fin 3) :
    remainingElement p i ^ p =
      algebraMap (S p) (chartRootAlgebra p) (algebraMap C (S p) (remainingForm i)) := by
  apply Subtype.ext
  change remainingRoot p i ^ p =
    algebraMap (S p) (L p) (algebraMap C (S p) (remainingForm i))
  rw [← IsScalarTower.algebraMap_apply C (S p) (L p)]
  exact remainingRoot_pow p i

lemma remainingElement_isUnit (i : Fin 3) : IsUnit (remainingElement p i) := by
  rw [← isUnit_pow_iff (NeZero.ne p), remainingElement_pow]
  exact (remaining_unit p i).map (algebraMap (S p) (chartRootAlgebra p))

def remainingUnit (i : Fin 3) : (chartRootAlgebra p)ˣ :=
  (remainingElement_isUnit p i).unit

@[simp] lemma remainingUnit_val (i : Fin 3) :
    (remainingUnit p i : chartRootAlgebra p) = remainingElement p i :=
  IsUnit.unit_spec _

lemma remainingUnit_to_field (i : Fin 3) :
    algebraMap (chartRootAlgebra p) (L p) (remainingUnit p i : chartRootAlgebra p) =
      remainingRoot p i := by
  rw [remainingUnit_val]
  rfl

local instance : IsScalarTower (B 7) (chartRootAlgebra 7) (L 7) :=
  CanonicalCoordinates.towerViaMiddle (B 7) (S 7) (chartRootAlgebra 7) (L 7)
local instance : IsScalarTower ℂ (chartRootAlgebra 7) (L 7) :=
  CanonicalCoordinates.towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (L 7) Ω[L 7⁄ℂ] := CanonicalCoordinates.kaehlerModule ℂ (L 7)
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorSMul _ _
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorMulAction _ _
local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.topModule _ _
local instance : SMul (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  (CanonicalCoordinates.topModule _ _).toSMul

lemma chartCoordinate_to_field (i : Fin 2) :
    algebraMap (chartRootAlgebra 7) (L 7) (chartCoordinate 7 i) = coordinateRoot 7 i := by
  rw [chartCoordinate, ← IsScalarTower.algebraMap_apply (B 7) (chartRootAlgebra 7) (L 7)]
  rfl

def canonicalUnit : (chartRootAlgebra 7)ˣ :=
  -((exponent_unit 7).map (algebraMap (S 7) (chartRootAlgebra 7))).unit ^ 2 *
    (remainingUnit 7 0 ^ 1 * remainingUnit 7 1 ^ 6 * remainingUnit 7 2 ^ 6)⁻¹

lemma canonicalUnit_to_field :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      -49 / (root 7 0 ^ 1 * root 7 1 ^ 6 * (root 7 2 / root 7 3) ^ 6) := by
  have hneg (a : chartRootAlgebra 7) :
      algebraMap (chartRootAlgebra 7) (L 7) (-a) =
        -algebraMap (chartRootAlgebra 7) (L 7) a :=
    (algebraMap (chartRootAlgebra 7) (L 7)).map_neg a
  simp only [canonicalUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, map_mul, map_pow, hneg, map_units_inv,
    remainingUnit_to_field, IsUnit.unit_spec, map_natCast]
  change -(7 : L 7)^2 * (root 7 0 ^ 1 * root 7 1 ^ 6 * (root 7 2 / root 7 3) ^ 6)⁻¹ = _
  norm_num [div_eq_mul_inv]

lemma canonical_density_identity :
    ExplicitCone.sectionCoefficient (0,0)^5 *
      (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6) /
        (∏ i : Fin 5, root 7 i)^6 =
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) := by
  rw [canonicalUnit_to_field]
  have h0 := root_ne_zero 7 0
  have h1 := root_ne_zero 7 1
  have h2 := root_ne_zero 7 2
  have h3 := root_ne_zero 7 3
  have h4 := root_ne_zero 7 4
  have hc : ExplicitCone.sectionCoefficient (0,0) = root 7 0 * root 7 3 := by
    change (1 : L 7) * root 7 0 * root 7 3 = _
    simp only [one_mul]
  have hp : (∏ i : Fin 5, root 7 i) =
      root 7 0 * root 7 1 * root 7 2 * root 7 3 * root 7 4 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change root 7 0 * (root 7 1 * (root 7 2 * (root 7 3 * root 7 4))) = _
    ring
  rw [hc, hp]
  change (root 7 0 * root 7 3)^5 *
    (-49 * (root 7 3)^13 * (root 7 4 / root 7 3)^6) / _ = _
  field_simp [h0,h1,h2,h3,h4]

def canonicalFrame : Basis Unit (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.unitTopBasis (cotangentBasis 7) canonicalUnit

lemma canonicalFrame_to_field :
    CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
      (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) =
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) •
      (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
        ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1))) := by
  have hf := CanonicalCoordinates.exteriorMap_frame ℂ (chartRootAlgebra 7) (L 7)
    (cotangentBasis 7) canonicalUnit (chartCoordinate 7) (cotangentBasis_apply 7)
  change CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
    (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) = _ at hf
  simpa only [chartCoordinate_to_field] using hf

lemma canonicalForm_eq : KummerTriple.canonicalForm =
    (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
      (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6)) •
      (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
        ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1))) := by
  rw [KummerTriple.canonicalForm, original_x, original_y,
    CanonicalCoordinates.coordinateJacobian_shiftedDiagonal, smul_smul]

lemma canonical_density_scalar :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      ExplicitCone.sectionCoefficient (0,0)^5 *
        (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
          (-49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6)) := by
  rw [← canonical_density_identity]
  ring

lemma canonicalFrame_rational :
    CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
      (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) =
    ExplicitCone.sectionCoefficient (0,0)^5 • KummerTriple.canonicalForm := by
  rw [canonicalFrame_to_field, canonicalForm_eq, smul_smul]
  exact congrArg (fun a : L 7 => a •
    (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
      ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1)))) canonical_density_scalar

end KummerShiftedDiagonal

end

end OAI
