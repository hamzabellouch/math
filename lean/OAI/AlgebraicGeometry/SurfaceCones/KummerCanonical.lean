import OAI.AlgebraicGeometry.SurfaceCones.KummerGalois
import OAI.AlgebraicGeometry.SurfaceCones.CotangentCoordinates

namespace OAI

/-! The triple-point chart has p^3 étale sheets over its ramified-coordinate algebra. -/
noncomputable section
open Algebra MvPolynomial
namespace KummerTriple
open KummerLines
variable (p : ℕ) [Fact p.Prime]

lemma coordinateRoot_mem_coordinateField (i : Fin 2) :
    coordinateRoot p i ∈ coordinateField p := by
  have h (j : Fin 2) : root p (Fin.castAdd 3 j) ∈ coordinateField p :=
    IntermediateField.subset_adjoin K _ (Set.mem_range_self j)
  fin_cases i
  · exact h 0
  · exact (coordinateField p).div_mem (h 1) (h 0)

lemma coordinateAlgebra_le_coordinateField :
    B p ≤ (coordinateField p).toSubalgebra.restrictScalars ℂ := by
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  exact coordinateRoot_mem_coordinateField p i

local instance coordinateFieldAlgebra : Algebra (B p) (coordinateField p) :=
  (Subalgebra.inclusion (coordinateAlgebra_le_coordinateField p)).toAlgebra
local instance : SMul (B p) (coordinateField p) :=
  @Algebra.toSMul (B p) (coordinateField p) _ _ (coordinateFieldAlgebra p)
local instance : SMul (B p) (L p) :=
  @Algebra.toSMul (B p) (L p) _ _ (coordinateAlgebra p).toAlgebra
local instance : IsScalarTower (B p) (coordinateField p) (L p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : FaithfulSMul (B p) (coordinateField p) :=
  Subalgebra.inclusion.faithfulSMul (coordinateAlgebra_le_coordinateField p)

lemma coordinateField_fractionRing : IsFractionRing (B p) (coordinateField p) := by
  let G := IntermediateField.adjoin ℂ (Set.range (coordinateRoot p))
  have hroot (i : Fin 2) : coordinateRoot p i ∈ G :=
    IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)
  have hR (a : R) : algebraMap R (L p) a ∈ G := by
    induction a using MvPolynomial.induction_on with
    | C z => exact G.algebraMap_mem z
    | add a b ha hb => simpa only [map_add] using G.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul]
      apply G.mul_mem ha
      fin_cases j
      · change algebraMap R (L p) (X 0) ∈ G
        rw [← coordinateRoot_zero_pow p]
        exact G.toSubalgebra.pow_mem (hroot 0) p
      · change algebraMap R (L p) (lineForm 1) ∈ G
        rw [← root_pow p 1, original_root_one p]
        exact G.toSubalgebra.pow_mem (G.mul_mem (hroot 0) (hroot 1)) p
  have hK (z : K) : algebraMap K (L p) z ∈ G := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
    rw [map_div₀, ← IsScalarTower.algebraMap_apply R K (L p),
      ← IsScalarTower.algebraMap_apply R K (L p)]
    exact G.div_mem (hR a) (hR b)
  have hgen (i : Fin 2) : root p (Fin.castAdd 3 i) ∈ G := by
    fin_cases i
    · exact hroot 0
    · change root p 1 ∈ G
      rw [original_root_one p]
      exact G.mul_mem (hroot 0) (hroot 1)
  have hle : ∀ x ∈ coordinateField p, x ∈ G := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hgen i
    | algebraMap x => exact hK x
    | add x y hx hy h₁ h₂ => exact G.add_mem h₁ h₂
    | mul x y hx hy h₁ h₂ => exact G.mul_mem h₁ h₂
    | inv x hx h₁ => exact G.inv_mem h₁
  apply IsFractionRing.of_field
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, he⟩ := IntermediateField.mem_adjoin_iff_div.mp (hle x hx)
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
  exact Subtype.ext he

local instance bRootAlgebra : Algebra (B p) (chartRootAlgebra p) :=
  ((algebraMap (S p) (chartRootAlgebra p)).comp (algebraMap (B p) (S p))).toAlgebra
local instance : SMul (B p) (chartRootAlgebra p) :=
  @Algebra.toSMul (B p) (chartRootAlgebra p) _ _ (bRootAlgebra p)
local instance : Module (B p) (chartRootAlgebra p) :=
  @Algebra.toModule (B p) (chartRootAlgebra p) _ _ (bRootAlgebra p)
local instance : IsScalarTower (B p) (S p) (chartRootAlgebra p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower (B p) (chartRootAlgebra p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq (B p) (S p) (L p),
      IsScalarTower.algebraMap_eq (S p) (chartRootAlgebra p) (L p)]
    rfl)

lemma chartRootAlgebra_degree : Module.finrank (S p) (chartRootAlgebra p) = p ^ 3 := by
  let := coordinateField_fractionRing p
  rw [IsLocalization.finrank_eq (S p) (Submonoid.powers (bDenominator p))
    (bPowers_le p)]
  exact (IsFractionRing.finrank_eq (B p) (coordinateField p)
    (chartRootAlgebra p) (L p)).symm.trans (coordinateField_degree p)

end KummerTriple


end

/-! Cotangent bases and Jacobians in the étale Kummer charts. -/
noncomputable section
open Algebra TensorProduct KaehlerDifferential Module

namespace KummerTriple
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

local instance : SMul (chartRootAlgebra p)
    (ExteriorAlgebra (chartRootAlgebra p) Ω[chartRootAlgebra p⁄ℂ]) :=
  CanonicalCoordinates.exteriorSMul _ _

/-- In particular the chart map to the affine plane has the
Jacobian 49 u^13 v^6. The two coordinates are the source roots
u = y₀ and v = y₁/y₀. -/
lemma cotangentJacobian_seven :
    ExteriorAlgebra.ι (chartRootAlgebra p) (D ℂ _ ((chartCoordinate p 0) ^ 7)) *
      ExteriorAlgebra.ι (chartRootAlgebra p) (D ℂ _ ((chartCoordinate p 0 * chartCoordinate p 1) ^ 7)) =
    (49 * (chartCoordinate p 0) ^ 13 * (chartCoordinate p 1) ^ 6) •
      (ExteriorAlgebra.ι (chartRootAlgebra p) (D ℂ _ (chartCoordinate p 0)) *
        ExteriorAlgebra.ι (chartRootAlgebra p) (D ℂ _ (chartCoordinate p 1))) :=
  CanonicalCoordinates.coordinateJacobian_seven (D ℂ _) (chartCoordinate p 0)
    (chartCoordinate p 1)

end KummerTriple


end

/-! The unit coefficient of the canonical form on a triple-point normalization chart. -/
noncomputable section
open Algebra
namespace KummerTriple
open KummerLines
variable (p : ℕ) [Fact p.Prime]

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

/-- Unit multiplying du∧dv in the canonical frame c₀₀⁵ ω at n=7. -/
def canonicalUnit : (chartRootAlgebra 7)ˣ :=
  ((exponent_unit 7).map (algebraMap (S 7) (chartRootAlgebra 7))).unit ^ 2 *
    (remainingUnit 7 0 ^ 6 * remainingUnit 7 1 * remainingUnit 7 2 ^ 6)⁻¹

lemma canonicalUnit_to_field :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      49 / (root 7 2 ^ 6 * root 7 3 * (root 7 4 / root 7 0) ^ 6) := by
  simp only [canonicalUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    map_mul, map_pow, map_units_inv, remainingUnit_to_field, IsUnit.unit_spec,
    map_natCast]
  change (7 : L 7) ^ 2 *
    (root 7 2 ^ 6 * root 7 3 * (root 7 4 / root 7 0) ^ 6)⁻¹ = _
  norm_num [div_eq_mul_inv]

/-- Exact Jacobian coefficient after multiplication by the fifth power of
sectionCoefficient (0,0). All entries are roots in L. -/
lemma canonical_density_identity :
    ExplicitCone.sectionCoefficient (0, 0) ^ 5 *
        (49 * (root 7 0) ^ 13 * (root 7 1 / root 7 0) ^ 6) /
      (∏ i : Fin 5, root 7 i) ^ 6 =
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) := by
  rw [canonicalUnit_to_field]
  have h0 := root_ne_zero 7 0
  have h1 := root_ne_zero 7 1
  have h2 := root_ne_zero 7 2
  have h3 := root_ne_zero 7 3
  have h4 := root_ne_zero 7 4
  have hc : ExplicitCone.sectionCoefficient (0, 0) = root 7 0 * root 7 3 := by
    change (1 : L 7) * root 7 0 * root 7 3 = _
    simp only [one_mul]
  rw [hc]
  have hp : (∏ i : Fin 5, root 7 i) =
      root 7 0 * root 7 1 * root 7 2 * root 7 3 * root 7 4 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change root 7 0 * (root 7 1 * (root 7 2 * (root 7 3 * root 7 4))) = _
    ring
  rw [hp]
  field_simp [h0, h1, h2, h3, h4]

end KummerTriple

end

/-! Bases of the second exterior power of a rank-two module. -/
noncomputable section
open Module KaehlerDifferential
namespace KummerTriple
local instance : Algebra ℂ (chartRootAlgebra 7) := canonicalCAlgebra 7
local instance : SMul ℂ (chartRootAlgebra 7) :=
  @Algebra.toSMul ℂ (chartRootAlgebra 7) _ _ (canonicalCAlgebra 7)
local instance : Module ℂ (chartRootAlgebra 7) :=
  @Algebra.toModule ℂ (chartRootAlgebra 7) _ _ (canonicalCAlgebra 7)
local instance : Module (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ] :=
  CanonicalCoordinates.kaehlerModule ℂ (chartRootAlgebra 7)

local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.topModule _ _
local instance : SMul (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  (CanonicalCoordinates.topModule _ _).toSMul

/-- The regular frame expressed rationally as c₀₀⁵ dx∧dy/(∏yᵢ)^6.
It is constructed in the determinant module. -/
def canonicalFrame : Basis Unit (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.unitTopBasis (cotangentBasis 7) canonicalUnit

lemma canonicalFrame_apply : canonicalFrame () =
    (canonicalUnit : chartRootAlgebra 7) •
      exteriorPower.ιMulti (chartRootAlgebra 7) 2
        (fun i => D ℂ _ (chartCoordinate 7 i)) := by
  have he : (cotangentBasis 7 : Fin 2 → Ω[chartRootAlgebra 7⁄ℂ]) =
      (fun i => D ℂ _ (chartCoordinate 7 i)) := funext (cotangentBasis_apply 7)
  exact (CanonicalCoordinates.unitTopBasis_apply (cotangentBasis 7) canonicalUnit).trans
    (congrArg (fun f => (canonicalUnit : chartRootAlgebra 7) •
      exteriorPower.ιMulti (chartRootAlgebra 7) 2 f) he)

end KummerTriple

end

/-! A rational top form and its regular canonical frame on the triple-point chart. -/
noncomputable section
open Module KaehlerDifferential
namespace KummerTriple
open KummerLines
local instance : Algebra (B 7) (chartRootAlgebra 7) := canonicalBRootAlgebra 7
local instance : SMul (B 7) (chartRootAlgebra 7) :=
  @Algebra.toSMul (B 7) (chartRootAlgebra 7) _ _ (canonicalBRootAlgebra 7)
local instance : Module (B 7) (chartRootAlgebra 7) :=
  @Algebra.toModule (B 7) (chartRootAlgebra 7) _ _ (canonicalBRootAlgebra 7)
local instance : Algebra ℂ (chartRootAlgebra 7) := canonicalCAlgebra 7
local instance : SMul ℂ (chartRootAlgebra 7) :=
  @Algebra.toSMul ℂ (chartRootAlgebra 7) _ _ (canonicalCAlgebra 7)
local instance : Module ℂ (chartRootAlgebra 7) :=
  @Algebra.toModule ℂ (chartRootAlgebra 7) _ _ (canonicalCAlgebra 7)
local instance : IsScalarTower (B 7) (chartRootAlgebra 7) (L 7) :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq (B 7) (S 7) (L 7),
      IsScalarTower.algebraMap_eq (S 7) (chartRootAlgebra 7) (L 7)]
    rfl)
local instance : IsScalarTower ℂ (B 7) (chartRootAlgebra 7) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ (chartRootAlgebra 7) (L 7) :=
  CanonicalCoordinates.towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ] :=
  CanonicalCoordinates.kaehlerModule ℂ (chartRootAlgebra 7)
local instance : SMul (chartRootAlgebra 7)
    (ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorSMul _ _
local instance : Module (L 7) Ω[L 7⁄ℂ] := CanonicalCoordinates.kaehlerModule ℂ (L 7)
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorSMul _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  CanonicalCoordinates.exteriorMulAction _ _
local instance : Algebra.FormallyEtale (chartRootAlgebra 7) (L 7) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (chartRootAlgebra 7))

lemma chartCoordinate_to_field (i : Fin 2) :
    algebraMap (chartRootAlgebra 7) (L 7) (chartCoordinate 7 i) = coordinateRoot 7 i := by
  rw [chartCoordinate, ← IsScalarTower.algebraMap_apply (B 7) (chartRootAlgebra 7) (L 7)]
  rfl

def rationalCotangentBasis : Basis (Fin 2) (L 7) Ω[L 7⁄ℂ] :=
  CanonicalCoordinates.rationalBasis ℂ (chartRootAlgebra 7) (L 7) (cotangentBasis 7)

lemma rationalCotangentBasis_apply (i : Fin 2) :
    rationalCotangentBasis i = D ℂ (L 7) (coordinateRoot 7 i) := by
  rw [rationalCotangentBasis, CanonicalCoordinates.rationalBasis_apply,
    cotangentBasis_apply, KaehlerDifferential.map_D, chartCoordinate_to_field]

/-- The source's rational 2-form dx∧dy/(y₀y₁y₂y₃y₄)^6. -/
def canonicalForm : ExteriorAlgebra (L 7) Ω[L 7⁄ℂ] :=
  ((∏ i : Fin 5, root 7 i)^6)⁻¹ •
    (ExteriorAlgebra.ι (L 7) (D ℂ _ (algebraMap R (L 7) (MvPolynomial.X 0))) *
      ExteriorAlgebra.ι (L 7) (D ℂ _ (algebraMap R (L 7) (MvPolynomial.X 1))))

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

lemma canonicalForm_eq : canonicalForm =
    (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
      (49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6)) •
      (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
        ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1))) := by
  rw [canonicalForm, ← coordinateRoot_zero_pow 7]
  have hy : algebraMap R (L 7) (MvPolynomial.X 1) =
      (coordinateRoot 7 0 * coordinateRoot 7 1)^7 := by
    rw [← original_root_one 7]
    exact (root_pow 7 1).symm
  rw [hy, CanonicalCoordinates.coordinateJacobian_seven, smul_smul]

lemma canonical_density_scalar :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      ExplicitCone.sectionCoefficient (0,0)^5 *
        (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
          (49 * (coordinateRoot 7 0)^13 * (coordinateRoot 7 1)^6)) := by
  rw [← canonical_density_identity]
  change _ = ExplicitCone.sectionCoefficient (0,0)^5 *
    (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
      (49 * (root 7 0)^13 * (root 7 1 / root 7 0)^6))
  ring

lemma canonicalFrame_rational :
    CanonicalCoordinates.exteriorMap ℂ (chartRootAlgebra 7) (L 7)
      (canonicalFrame () : ExteriorAlgebra (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ]) =
    ExplicitCone.sectionCoefficient (0,0)^5 • canonicalForm := by
  rw [canonicalFrame_to_field, canonicalForm_eq, smul_smul]
  exact congrArg (fun a : L 7 => a •
    (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
      ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1)))) canonical_density_scalar

end KummerTriple

end

end OAI
