import OAI.AlgebraicGeometry.SurfaceCones.KummerCanonicalCharts
import OAI.AlgebraicGeometry.SurfaceCones.KummerSectionAffineOpen

namespace OAI

/-! A canonical frame on the ordinary-node affine normalization chart. -/
noncomputable section
open Algebra Module KaehlerDifferential
namespace CanonicalCoordinates
@[instance_reducible] def subalgebraMonoid {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (S : Subalgebra R A) : Monoid S := inferInstance
variable {k A M : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M]
lemma coordinateJacobian_affine (d : Derivation k A M) (u v : A) :
    ExteriorAlgebra.ι A (d (v^7+1)) * ExteriorAlgebra.ι A (d (u^7)) =
    (-49 * u^6 * v^6) •
      (ExteriorAlgebra.ι A (d u) * ExteriorAlgebra.ι A (d v)) := by
  simp only [map_add, Derivation.map_one_eq_zero, add_zero,
    Derivation.leibniz_pow, Nat.reduceSub, ← Nat.cast_smul_eq_nsmul A,
    smul_smul, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [volume_swap, smul_neg, ← neg_smul]
  congr 1
  ring
end CanonicalCoordinates

namespace KummerAffineZero
open KummerLines
variable (p : ℕ) [Fact p.Prime]
abbrev root := KummerTriple.root
abbrev C := R
abbrev B := KummerAffineExtra.B p 0
abbrev S := KummerAffineExtra.S p 0
abbrev chartRootAlgebra := KummerAffineExtra.chartRootAlgebra p 0
local instance : Monoid (chartRootAlgebra p) := CanonicalCoordinates.subalgebraMonoid _
abbrev planeEquiv := KummerAffineExtra.planeEquiv p 0
abbrev bRoot := KummerAffineExtra.bRoot p 0
abbrev coordinateRoot := KummerAffineExtra.coordinateRoot p 0
abbrev chartRootAlgebra_finiteFreeEtale :=
  KummerAffineExtra.chartRootAlgebra_finiteFreeEtale p 0
abbrev remainingRoot := fun i =>
  KummerTriple.root p (KummerAffineExtra.remainingIndex 0 i)
abbrev remainingForm := fun i => lineForm (KummerAffineExtra.remainingIndex 0 i)
abbrev remainingRoot_mem_chartRootAlgebra := fun i =>
  KummerAffineExtra.remainingRoot_mem_chartRootAlgebra p 0 i
abbrev remaining_unit := fun i => KummerAffineExtra.remaining_unit p 0 i
abbrev exponent_unit := KummerAffineExtra.exponent_unit p 0
abbrev root_ne_zero := KummerTriple.root_ne_zero
lemma remainingRoot_pow (i : Fin 3) : remainingRoot p i ^ p =
    algebraMap C (L p) (remainingForm i) := KummerTriple.root_pow p _
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
    (remainingUnit 7 0 ^ 1 * remainingUnit 7 1 ^ 1 * remainingUnit 7 2 ^ 6)⁻¹

lemma canonicalUnit_to_field :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      -49 / (root 7 0 ^ 1 * root 7 3 ^ 1 * root 7 4 ^ 6) := by
  have hneg (a : chartRootAlgebra 7) :
      algebraMap (chartRootAlgebra 7) (L 7) (-a) =
        -algebraMap (chartRootAlgebra 7) (L 7) a :=
    (algebraMap (chartRootAlgebra 7) (L 7)).map_neg a
  simp only [canonicalUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, map_mul, map_pow, hneg, map_units_inv,
    remainingUnit_to_field, IsUnit.unit_spec, map_natCast]
  change -(7 : L 7)^2 * (root 7 0 ^ 1 * root 7 3 ^ 1 * root 7 4 ^ 6)⁻¹ = _
  norm_num [div_eq_mul_inv]

lemma canonical_density_identity :
    ExplicitCone.sectionCoefficient (0,0)^5 *
      (-49 * (coordinateRoot 7 0)^6 * (coordinateRoot 7 1)^6) /
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
    (-49 * (root 7 1)^6 * (root 7 2)^6) / _ = _
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
      (-49 * (coordinateRoot 7 0)^6 * (coordinateRoot 7 1)^6)) •
      (ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 0)) *
        ExteriorAlgebra.ι (L 7) (D ℂ _ (coordinateRoot 7 1))) := by
  rw [KummerTriple.canonicalForm]
  have hx : algebraMap R (L 7) (MvPolynomial.X 0) =
      (coordinateRoot 7 1)^7+1 := by
    change algebraMap R (L 7) (MvPolynomial.X 0) = root 7 2 ^ 7 + 1
    rw [KummerTriple.root_pow]
    change _ = algebraMap R (L 7) (MvPolynomial.X 0 - 1) + 1
    rw [map_sub, map_one]; ring
  have hy : algebraMap R (L 7) (MvPolynomial.X 1) =
      (coordinateRoot 7 0)^7 := (KummerTriple.root_pow 7 1).symm
  rw [hx, hy, CanonicalCoordinates.coordinateJacobian_affine, smul_smul]

lemma canonical_density_scalar :
    algebraMap (chartRootAlgebra 7) (L 7) (canonicalUnit : chartRootAlgebra 7) =
      ExplicitCone.sectionCoefficient (0,0)^5 *
        (((∏ i : Fin 5, root 7 i)^6)⁻¹ *
          (-49 * (coordinateRoot 7 0)^6 * (coordinateRoot 7 1)^6)) := by
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

end KummerAffineZero

end

/-! The canonical density is nonzero in the rational exterior module. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates
lemma scalar_nonzero {F N : Type*} [Field F] [AddCommGroup N] [Module F N]
    {a : F} {m : N} (ha : a ≠ 0) (hm : m ≠ 0) : a • m ≠ 0 := smul_ne_zero ha hm
lemma scalar_unique {F N : Type*} [Field F] [AddCommGroup N] [Module F N]
    {a b : F} {m : N} (hm : m ≠ 0) (h : a • m = b • m) : a = b :=
  smul_left_injective F hm h
lemma basis_volume_ne_zero {A M : Type*} [CommRing A] [Nontrivial A]
    [AddCommGroup M] [Module A M] (b : Basis (Fin 2) A M) :
    ExteriorAlgebra.ι A (b 0) * ExteriorAlgebra.ι A (b 1) ≠ 0 := by
  intro h
  apply (topBasis b).ne_zero ()
  apply Subtype.ext
  simpa only [topBasis_coe, Submodule.coe_zero] using h
end CanonicalCoordinates

namespace KummerTriple
open KummerLines CanonicalCoordinates
local instance : Module (L 7) Ω[L 7⁄ℂ] := kaehlerModule ℂ (L 7)
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorSMul _ _
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorMulAction _ _

lemma canonicalForm_ne_zero : canonicalForm ≠ 0 := by
  have hv := basis_volume_ne_zero rationalCotangentBasis
  simp only [rationalCotangentBasis_apply] at hv
  rw [canonicalForm_eq]
  apply scalar_nonzero _ hv
  apply mul_ne_zero
  · exact inv_ne_zero (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr
      fun i _ => root_ne_zero 7 i))
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (root_ne_zero 7 0))
    · exact pow_ne_zero _ (div_ne_zero (root_ne_zero 7 1) (root_ne_zero 7 0))

end KummerTriple

namespace SourceSymmetry
open ExplicitCone CanonicalCoordinates
local instance : Module L Ω[L⁄ℂ] := kaehlerModule ℂ L
local instance : SMul L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorSMul _ _
local instance : Module L (ExteriorAlgebra L Ω[L⁄ℂ]) := canonicalExteriorModule _ _
local instance : MulAction L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorMulAction _ _

lemma canonicalDensity_ne_zero (t : SectionIndex) : canonicalDensity t ≠ 0 :=
  scalar_nonzero (pow_ne_zero _ (coefficient_ne_zero t)) KummerTriple.canonicalForm_ne_zero

/-- Exact fifth-power transition, in the common fraction field. -/
lemma canonicalDensity_ratio (s t : SectionIndex) :
    canonicalDensity s = (sectionCoefficient s / sectionCoefficient t)^5 • canonicalDensity t := by
  rw [canonicalDensity, canonicalDensity, smul_smul, ← mul_pow,
    div_mul_cancel₀ _ (coefficient_ne_zero t)]

lemma canonicalDensity_scalar_unique (s t : SectionIndex) {a : L}
    (h : canonicalDensity s = a • canonicalDensity t) :
    a = (sectionCoefficient s / sectionCoefficient t)^5 := by
  have he := (canonicalDensity_ratio s t).symm.trans h
  exact (scalar_unique (canonicalDensity_ne_zero t) he).symm
end SourceSymmetry

end

/-! Top cotangent modules and their images in rational differential forms. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates
@[instance_reducible] def rationalExteriorAlgebra (F M : Type*) [CommRing F]
    [AddCommGroup M] [Module F M] : Algebra F (ExteriorAlgebra F M) := inferInstance
theorem rationalExteriorTower (A F M : Type*) [CommRing A] [CommRing F]
    [Algebra A F] [AddCommGroup M] [Module A M] [Module F M]
    [IsScalarTower A F M] :
    IsScalarTower A F (ExteriorAlgebra F M) := inferInstance
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

lemma unitBasis_repr (b : Basis Unit A M) (m : M) :
    (b.repr m ()) • b () = m := by
  simpa only [Fintype.sum_unique] using b.sum_repr m

lemma rankOne_range (b : Basis Unit A M) (f : M →ₗ[A] N) :
    LinearMap.range f = Submodule.span A {f (b ())} := by
  apply le_antisymm
  · rintro _ ⟨m,rfl⟩
    have he : f m = (b.repr m ()) • f (b ()) := by
      calc
        f m = f ((b.repr m ()) • b ()) := congrArg f (unitBasis_repr b m).symm
        _ = _ := f.map_smul _ _
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro _ rfl
    exact LinearMap.mem_range_self f _

lemma rankOne_injective {F : Type*} [Field F] [Algebra A F] [Module F N]
    [IsScalarTower A F N] (b : Basis Unit A M) (f : M →ₗ[A] N)
    (hinj : Function.Injective (algebraMap A F)) (hf : f (b ()) ≠ 0) :
    Function.Injective f := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro m hm
  have he : algebraMap A F (b.repr m ()) • f (b ()) = 0 := by
    rw [IsScalarTower.algebraMap_smul F, ← map_smul, unitBasis_repr b m]
    exact hm
  have hz : b.repr m () = 0 := hinj (by
    exact ((smul_eq_zero.mp he).resolve_right hf).trans (map_zero (algebraMap A F)).symm)
  rw [← unitBasis_repr b m, hz, zero_smul]

variable (k A F : Type*) [CommRing k] [CommRing A] [CommRing F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]

/-- The natural map from the determinant module to rational forms. -/
def determinantMap : (⋀[A]^2 Ω[A⁄k]) →ₗ[A] ExteriorAlgebra F Ω[F⁄k] :=
  (exteriorMap k A F).toLinearMap.comp (Submodule.subtype _)

lemma determinantMap_apply (m : ⋀[A]^2 Ω[A⁄k]) :
    determinantMap k A F m = exteriorMap k A F (m : ExteriorAlgebra A Ω[A⁄k]) := rfl

lemma determinantImage (b : Basis Unit A (⋀[A]^2 Ω[A⁄k])) :
    LinearMap.range (determinantMap k A F) =
      Submodule.span A {exteriorMap k A F (b () : ExteriorAlgebra A Ω[A⁄k])} :=
  rankOne_range b _

end CanonicalCoordinates

end

/-! Determinant frames on the five affine normalization opens. -/
noncomputable section
open Module KaehlerDifferential

namespace KummerTriple
open KummerLines CanonicalCoordinates
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
  towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ] :=
  kaehlerModule ℂ (chartRootAlgebra 7)
local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) := topModule _ _
local instance : Module (L 7) Ω[L 7⁄ℂ] := kaehlerModule ℂ (L 7)
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorSMul _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorMulAction _ _
local instance : Algebra (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := rationalExteriorAlgebra _ _
local instance : IsScalarTower (chartRootAlgebra 7) (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

lemma canonicalImage :
    LinearMap.range (determinantMap ℂ (chartRootAlgebra 7) (L 7)) =
      Submodule.span (chartRootAlgebra 7) {SourceSymmetry.canonicalDensity (0,0)} := by
  rw [determinantImage ℂ (chartRootAlgebra 7) (L 7) canonicalFrame,
    canonicalFrame_rational]
  rfl

lemma determinantMap_injective :
    Function.Injective (determinantMap ℂ (chartRootAlgebra 7) (L 7)) := by
  apply rankOne_injective (F := L 7) canonicalFrame _ (show
    Function.Injective (algebraMap (chartRootAlgebra 7) (L 7)) from Subtype.val_injective)
  rw [determinantMap_apply, canonicalFrame_rational]
  exact SourceSymmetry.canonicalDensity_ne_zero (0,0)

end KummerTriple

namespace KummerTripleDiagonal
open KummerLines CanonicalCoordinates
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
  towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ] :=
  kaehlerModule ℂ (chartRootAlgebra 7)
local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) := topModule _ _
local instance : Module (L 7) Ω[L 7⁄ℂ] := kaehlerModule ℂ (L 7)
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorSMul _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorMulAction _ _
local instance : Algebra (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := rationalExteriorAlgebra _ _
local instance : IsScalarTower (chartRootAlgebra 7) (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

lemma canonicalImage :
    LinearMap.range (determinantMap ℂ (chartRootAlgebra 7) (L 7)) =
      Submodule.span (chartRootAlgebra 7) {SourceSymmetry.canonicalDensity (0,0)} := by
  rw [determinantImage ℂ (chartRootAlgebra 7) (L 7) canonicalFrame,
    canonicalFrame_rational]
  rfl

lemma determinantMap_injective :
    Function.Injective (determinantMap ℂ (chartRootAlgebra 7) (L 7)) := by
  apply rankOne_injective (F := L 7) canonicalFrame _ (show
    Function.Injective (algebraMap (chartRootAlgebra 7) (L 7)) from Subtype.val_injective)
  rw [determinantMap_apply, canonicalFrame_rational]
  exact SourceSymmetry.canonicalDensity_ne_zero (0,0)

end KummerTripleDiagonal

namespace KummerShifted
open KummerLines CanonicalCoordinates
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
  towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ] :=
  kaehlerModule ℂ (chartRootAlgebra 7)
local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) := topModule _ _
local instance : Module (L 7) Ω[L 7⁄ℂ] := kaehlerModule ℂ (L 7)
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorSMul _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorMulAction _ _
local instance : Algebra (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := rationalExteriorAlgebra _ _
local instance : IsScalarTower (chartRootAlgebra 7) (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

lemma canonicalImage :
    LinearMap.range (determinantMap ℂ (chartRootAlgebra 7) (L 7)) =
      Submodule.span (chartRootAlgebra 7) {SourceSymmetry.canonicalDensity (0,0)} := by
  rw [determinantImage ℂ (chartRootAlgebra 7) (L 7) canonicalFrame,
    canonicalFrame_rational]
  rfl

lemma determinantMap_injective :
    Function.Injective (determinantMap ℂ (chartRootAlgebra 7) (L 7)) := by
  apply rankOne_injective (F := L 7) canonicalFrame _ (show
    Function.Injective (algebraMap (chartRootAlgebra 7) (L 7)) from Subtype.val_injective)
  rw [determinantMap_apply, canonicalFrame_rational]
  exact SourceSymmetry.canonicalDensity_ne_zero (0,0)

end KummerShifted

namespace KummerShiftedDiagonal
open KummerLines CanonicalCoordinates
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
  towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ] :=
  kaehlerModule ℂ (chartRootAlgebra 7)
local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) := topModule _ _
local instance : Module (L 7) Ω[L 7⁄ℂ] := kaehlerModule ℂ (L 7)
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorSMul _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorMulAction _ _
local instance : Algebra (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := rationalExteriorAlgebra _ _
local instance : IsScalarTower (chartRootAlgebra 7) (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

lemma canonicalImage :
    LinearMap.range (determinantMap ℂ (chartRootAlgebra 7) (L 7)) =
      Submodule.span (chartRootAlgebra 7) {SourceSymmetry.canonicalDensity (0,0)} := by
  rw [determinantImage ℂ (chartRootAlgebra 7) (L 7) canonicalFrame,
    canonicalFrame_rational]
  rfl

lemma determinantMap_injective :
    Function.Injective (determinantMap ℂ (chartRootAlgebra 7) (L 7)) := by
  apply rankOne_injective (F := L 7) canonicalFrame _ (show
    Function.Injective (algebraMap (chartRootAlgebra 7) (L 7)) from Subtype.val_injective)
  rw [determinantMap_apply, canonicalFrame_rational]
  exact SourceSymmetry.canonicalDensity_ne_zero (0,0)

end KummerShiftedDiagonal

namespace KummerAffineZero
open KummerLines CanonicalCoordinates
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
  towerViaMiddle ℂ (B 7) (chartRootAlgebra 7) (L 7)
local instance : Module (chartRootAlgebra 7) Ω[chartRootAlgebra 7⁄ℂ] :=
  kaehlerModule ℂ (chartRootAlgebra 7)
local instance : Module (chartRootAlgebra 7)
    (⋀[chartRootAlgebra 7]^2 Ω[chartRootAlgebra 7⁄ℂ]) := topModule _ _
local instance : Module (L 7) Ω[L 7⁄ℂ] := kaehlerModule ℂ (L 7)
local instance : Module (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  SourceSymmetry.canonicalExteriorModule _ _
local instance : SMul (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorSMul _ _
local instance : MulAction (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := exteriorMulAction _ _
local instance : Algebra (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) := rationalExteriorAlgebra _ _
local instance : IsScalarTower (chartRootAlgebra 7) (L 7) (ExteriorAlgebra (L 7) Ω[L 7⁄ℂ]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

lemma canonicalImage :
    LinearMap.range (determinantMap ℂ (chartRootAlgebra 7) (L 7)) =
      Submodule.span (chartRootAlgebra 7) {SourceSymmetry.canonicalDensity (0,0)} := by
  rw [determinantImage ℂ (chartRootAlgebra 7) (L 7) canonicalFrame,
    canonicalFrame_rational]
  rfl

lemma determinantMap_injective :
    Function.Injective (determinantMap ℂ (chartRootAlgebra 7) (L 7)) := by
  apply rankOne_injective (F := L 7) canonicalFrame _ (show
    Function.Injective (algebraMap (chartRootAlgebra 7) (L 7)) from Subtype.val_injective)
  rw [determinantMap_apply, canonicalFrame_rational]
  exact SourceSymmetry.canonicalDensity_ne_zero (0,0)

end KummerAffineZero

end

/-! Generators of the rational determinant image. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates
variable (k A F : Type*) [CommRing k] [CommRing A] [CommRing F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]

/-- A wedge of two rational differentials. -/
def rationalWedge (a b : F) : ExteriorAlgebra F Ω[F⁄k] :=
  ExteriorAlgebra.ι F (D k F a) * ExteriorAlgebra.ι F (D k F b)

lemma determinantMap_volume (a : Fin 2 → A) :
    determinantMap k A F (exteriorPower.ιMulti A 2 (fun i => D k A (a i))) =
      rationalWedge k F (algebraMap A F (a 0)) (algebraMap A F (a 1)) := by
  rw [determinantMap_apply]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, Matrix.vecTail, Function.comp_apply, mul_one, map_mul, exteriorMap_D, rationalWedge]
  rfl

lemma determinantMap_generators :
    LinearMap.range (determinantMap k A F) =
      Submodule.span A (Set.range (fun a : Fin 2 → A =>
        rationalWedge k F (algebraMap A F (a 0)) (algebraMap A F (a 1)))) := by
  have hs := exteriorPower.ιMulti_span_of_span A 2 Ω[A⁄k]
    (KaehlerDifferential.span_range_derivation k A)
  rw [LinearMap.range_eq_map, ← hs, LinearMap.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨x,⟨u,hu,rfl⟩,rfl⟩
    choose a ha using fun i => hu (Set.mem_range_self i)
    have hu' : u = fun i => D k A (a i) := funext (fun i => (ha i).symm)
    exact ⟨a,by rw [hu', determinantMap_volume]⟩
  · rintro ⟨a,rfl⟩
    refine ⟨exteriorPower.ιMulti A 2 (fun i => D k A (a i)), ?_, determinantMap_volume k A F a⟩
    refine ⟨fun i => D k A (a i), ?_, rfl⟩
    rintro _ ⟨i,rfl⟩
    exact Set.mem_range_self (a i)

end CanonicalCoordinates

end

/-! Localization of the determinant image. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates
variable (k A F : Type*) [CommRing k] [CommRing A] [CommRing F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]

lemma determinantMap_generators_of_derivations {I : Type*} (g : I → A)
    (hg : Submodule.span A (Set.range (fun i => D k A (g i))) = ⊤) :
    LinearMap.range (determinantMap k A F) =
      Submodule.span A (Set.range (fun a : Fin 2 → I =>
        rationalWedge k F (algebraMap A F (g (a 0))) (algebraMap A F (g (a 1))))) := by
  have hs := exteriorPower.ιMulti_span_of_span A 2 Ω[A⁄k] hg
  rw [LinearMap.range_eq_map, ← hs, LinearMap.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨x,⟨u,hu,rfl⟩,rfl⟩
    choose a ha using fun i => hu (Set.mem_range_self i)
    have hu' : u = fun i => D k A (g (a i)) := funext (fun i => (ha i).symm)
    exact ⟨a,by rw [hu', determinantMap_volume]⟩
  · rintro ⟨a,rfl⟩
    refine ⟨exteriorPower.ιMulti A 2 (fun i => D k A (g (a i))), ?_,
      determinantMap_volume k A F (g ∘ a)⟩
    refine ⟨fun i => D k A (g (a i)), ?_, rfl⟩
    rintro _ ⟨i,rfl⟩
    exact Set.mem_range_self (a i)

variable (B : Type*) [CommRing B] [Algebra k B] [Algebra A B] [Algebra B F]
  [IsScalarTower k A B] [IsScalarTower k B F] [IsScalarTower A B F]

lemma determinantImage_localization (s : Submonoid A) [IsLocalization s B] :
    LinearMap.range (determinantMap k B F) =
      Submodule.span B (LinearMap.range (determinantMap k A F) : Set (ExteriorAlgebra F Ω[F⁄k])) := by
  have hs : Submodule.span B (Set.range (fun a : A => D k B (algebraMap A B a))) = ⊤ := by
    simpa only [Function.comp_def, KaehlerDifferential.map_D] using
      KaehlerDifferential.span_range_map_derivation_of_isLocalization k A B s
  rw [determinantMap_generators_of_derivations k B F (algebraMap A B) hs,
    determinantMap_generators, Submodule.span_span_of_tower]
  simp only [IsScalarTower.algebraMap_apply A B F]

end CanonicalCoordinates

end

/-! Descent of determinant lattices across principal-open covers. -/
noncomputable section
namespace CanonicalCoordinates
variable (A : Type*) [CommRing A]
variable (M : Type*) [AddCommGroup M] [Module A M]
variable (s : Set A) (hs : Ideal.span s = ⊤)
variable (B : s → Type*) [∀ r, CommRing (B r)] [∀ r, Algebra A (B r)]
  [∀ r, IsLocalization.Away r.1 (B r)]
  [∀ r, Module (B r) M] [∀ r, IsScalarTower A (B r) M]

include hs in
lemma submodule_eq_of_local_spans (N P : Submodule A M)
    (h : ∀ r, Submodule.span (B r) (N : Set M) = Submodule.span (B r) (P : Set M)) :
    N = P := by
  let (r : s) : IsLocalizedModule.Away r.1 (LinearMap.id : M →ₗ[A] M) :=
    isLocalizedModule_id (.powers r.1) M (B r)
  apply Submodule.eq_of_isLocalized'_span s hs B (fun _ => M)
    (fun _ => (LinearMap.id : M →ₗ[A] M))
  intro r
  simpa only [Submodule.localized'_eq_span, LinearMap.id_coe, Set.image_id] using h r

end CanonicalCoordinates


open CanonicalCoordinates KaehlerDifferential
namespace FieldPrincipalOpen
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (A : Subalgebra k F) [IsFractionRing A F] (d : A) (hd : d ≠ 0)
local instance : IsScalarTower k A (away A d hd) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower A (away A d hd) F :=
  IsScalarTower.of_algebraMap_eq' rfl

lemma determinantImage_away :
    LinearMap.range (determinantMap k (away A d hd) F) =
      Submodule.span (away A d hd)
        (LinearMap.range (determinantMap k A F) : Set (ExteriorAlgebra F Ω[F⁄k])) :=
  determinantImage_localization k A F (away A d hd) (.powers d)

lemma determinantImage_away_frame (w : ExteriorAlgebra F Ω[F⁄k])
    (h : LinearMap.range (determinantMap k A F) = Submodule.span A {w}) :
    LinearMap.range (determinantMap k (away A d hd) F) =
      Submodule.span (away A d hd) {w} := by
  have ht : IsScalarTower A (away A d hd) (ExteriorAlgebra F Ω[F⁄k]) :=
    IsScalarTower.of_algebraMap_eq' rfl
  rw [determinantImage_away, h]
  exact @Submodule.span_span_of_tower A (ExteriorAlgebra F Ω[F⁄k]) (away A d hd)
    _ _ _ {w} _ _ _ ht

lemma determinantImage_congr {A B : Subalgebra k F} (h : A = B)
    (w : ExteriorAlgebra F Ω[F⁄k])
    (hw : LinearMap.range (determinantMap k B F) = Submodule.span B {w}) :
    LinearMap.range (determinantMap k A F) = Submodule.span A {w} := by
  subst B
  exact hw

variable (s : Set A) (hs : Ideal.span s = ⊤) (hs0 : ∀ d ∈ s, d ≠ 0)
include hs in
lemma determinantImage_of_away (w : ExteriorAlgebra F Ω[F⁄k])
    (h : ∀ r : s, LinearMap.range (determinantMap k (away A r.1 (hs0 r.1 r.2)) F) =
      Submodule.span (away A r.1 (hs0 r.1 r.2)) {w}) :
    LinearMap.range (determinantMap k A F) = Submodule.span A {w} := by
  have ht : ∀ r : s, IsScalarTower A (away A r.1 (hs0 r.1 r.2))
      (ExteriorAlgebra F Ω[F⁄k]) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  refine @submodule_eq_of_local_spans A _ (ExteriorAlgebra F Ω[F⁄k]) _ _ s hs
    (fun r => away A r.1 (hs0 r.1 r.2)) (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance) ht _ _ ?_
  intro r
  exact (determinantImage_away A r.1 (hs0 r.1 r.2)).symm.trans ((h r).trans
    (@Submodule.span_span_of_tower A (ExteriorAlgebra F Ω[F⁄k])
      (away A r.1 (hs0 r.1 r.2)) _ _ _ {w} _ _ _ (ht r)).symm)

end FieldPrincipalOpen

end

/-! The rational determinant lattice on the section chart c₀₀, computed using its five normalization opens. -/
noncomputable section
open KaehlerDifferential CanonicalCoordinates
namespace ExplicitCone
local instance (A : Subalgebra ℂ L) : Module A Ω[A⁄ℂ] := kaehlerModule ℂ A
local instance (A : Subalgebra ℂ L) : Module A (⋀[A]^2 Ω[A⁄ℂ]) := topModule _ _
local instance : Module L Ω[L⁄ℂ] := kaehlerModule ℂ L
local instance : Module L (ExteriorAlgebra L Ω[L⁄ℂ]) := SourceSymmetry.canonicalExteriorModule _ _

lemma tripleRegular_canonicalImage : LinearMap.range (determinantMap ℂ (tripleRegularAlgebra) L) =
    Submodule.span (tripleRegularAlgebra) {SourceSymmetry.canonicalDensity (0,0)} := by
  have h := KummerTriple.canonicalImage
  rw [determinantMap_generators] at h ⊢
  exact h

lemma diagonalRegular_canonicalImage : LinearMap.range (determinantMap ℂ (diagonalRegularAlgebra) L) =
    Submodule.span (diagonalRegularAlgebra) {SourceSymmetry.canonicalDensity (0,0)} := by
  have h := KummerTripleDiagonal.canonicalImage
  rw [determinantMap_generators] at h ⊢
  exact h

lemma shiftedRegular_canonicalImage : LinearMap.range (determinantMap ℂ (shiftedRegularAlgebra) L) =
    Submodule.span (shiftedRegularAlgebra) {SourceSymmetry.canonicalDensity (0,0)} := by
  have h := KummerShifted.canonicalImage
  rw [determinantMap_generators] at h ⊢
  exact h

lemma shiftedDiagonalRegular_canonicalImage : LinearMap.range (determinantMap ℂ (shiftedDiagonalRegularAlgebra) L) =
    Submodule.span (shiftedDiagonalRegularAlgebra) {SourceSymmetry.canonicalDensity (0,0)} := by
  have h := KummerShiftedDiagonal.canonicalImage
  rw [determinantMap_generators] at h ⊢
  exact h

lemma affineRegular_canonicalImage : LinearMap.range (determinantMap ℂ (affineRegularAlgebra 0) L) =
    Submodule.span (affineRegularAlgebra 0) {SourceSymmetry.canonicalDensity (0,0)} := by
  have h := KummerAffineZero.canonicalImage
  rw [determinantMap_generators] at h ⊢
  exact h

lemma affinePunctured_canonicalImage :
    LinearMap.range (determinantMap ℂ (affinePuncturedRegular 0) L) =
      Submodule.span (affinePuncturedRegular 0) {SourceSymmetry.canonicalDensity (0,0)} := by
  exact FieldPrincipalOpen.determinantImage_away_frame (affineRegularAlgebra 0)
    (affineFirstRoot 0) (affineFirstRoot_ne_zero 0) _ affineRegular_canonicalImage

def canonicalCoverDenominators : Fin 5 → sectionChart :=
  ![tripleSectionDenominator, diagonalSectionDenominator,
    shiftedSectionDenominator, shiftedDiagonalSectionDenominator,
    affineSectionDenominator 0]

lemma canonicalCoverDenominators_ne_zero (i : Fin 5) :
    canonicalCoverDenominators i ≠ 0 := by
  fin_cases i
  · exact tripleSectionDenominator_ne_zero
  · exact diagonalSectionDenominator_ne_zero
  · exact shiftedSectionDenominator_ne_zero
  · exact shiftedDiagonalSectionDenominator_ne_zero
  · exact affineSectionDenominator_ne_zero 0

lemma canonicalCoverDenominators_span :
    Ideal.span (Set.range canonicalCoverDenominators) = ⊤ := by
  by_contra h
  obtain ⟨P,hP,h⟩ := Ideal.exists_le_maximal _ h
  let := hP
  have hm (i : Fin 5) : canonicalCoverDenominators i ∈ P :=
    h (Ideal.subset_span (Set.mem_range_self i))
  rcases sectionChart_open_cover P with ht | hd | hs | hsd | ha
  · exact ht (hm 0)
  · exact hd (hm 1)
  · exact hs (hm 2)
  · exact hsd (hm 3)
  · exact ha (hm 4)

/-- The five principal-open coefficient algebras used to compute the determinant lattice. -/
def canonicalCoverOpen (i : Fin 5) : Subalgebra ℂ L :=
  FieldPrincipalOpen.away sectionChart (canonicalCoverDenominators i)
    (canonicalCoverDenominators_ne_zero i)

lemma canonicalCover_image (i : Fin 5) :
    LinearMap.range (determinantMap ℂ (canonicalCoverOpen i) L) =
      Submodule.span (canonicalCoverOpen i) {SourceSymmetry.canonicalDensity (0,0)} := by
  fin_cases i
  · change LinearMap.range (determinantMap ℂ (tripleSectionOpen) L) =
      Submodule.span (tripleSectionOpen) {SourceSymmetry.canonicalDensity (0,0)}
    exact FieldPrincipalOpen.determinantImage_congr (tripleSectionOpen_eq) _ tripleRegular_canonicalImage
  · change LinearMap.range (determinantMap ℂ (diagonalSectionOpen) L) =
      Submodule.span (diagonalSectionOpen) {SourceSymmetry.canonicalDensity (0,0)}
    exact FieldPrincipalOpen.determinantImage_congr (diagonalSectionOpen_eq) _ diagonalRegular_canonicalImage
  · change LinearMap.range (determinantMap ℂ (shiftedSectionOpen) L) =
      Submodule.span (shiftedSectionOpen) {SourceSymmetry.canonicalDensity (0,0)}
    exact FieldPrincipalOpen.determinantImage_congr (shiftedSectionOpen_eq) _ shiftedRegular_canonicalImage
  · change LinearMap.range (determinantMap ℂ (shiftedDiagonalSectionOpen) L) =
      Submodule.span (shiftedDiagonalSectionOpen) {SourceSymmetry.canonicalDensity (0,0)}
    exact FieldPrincipalOpen.determinantImage_congr (shiftedDiagonalSectionOpen_eq) _ shiftedDiagonalRegular_canonicalImage
  · change LinearMap.range (determinantMap ℂ (affineSectionOpen 0) L) =
      Submodule.span (affineSectionOpen 0) {SourceSymmetry.canonicalDensity (0,0)}
    exact FieldPrincipalOpen.determinantImage_congr (affineSectionOpen_eq 0) _ affinePunctured_canonicalImage

/-- The top-Kahler image. -/
lemma sectionChart_canonicalImage :
    LinearMap.range (determinantMap ℂ sectionChart L) =
      Submodule.span sectionChart {SourceSymmetry.canonicalDensity (0,0)} := by
  have hn : ∀ d ∈ Set.range canonicalCoverDenominators, d ≠ 0 := by
    rintro _ ⟨i,rfl⟩
    exact canonicalCoverDenominators_ne_zero i
  apply FieldPrincipalOpen.determinantImage_of_away sectionChart
    (Set.range canonicalCoverDenominators) canonicalCoverDenominators_span hn
  rintro ⟨_,i,rfl⟩
  exact canonicalCover_image i

end ExplicitCone

end

end OAI
