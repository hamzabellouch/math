import OAI.AlgebraicGeometry.SurfaceCones.SectionCompletion

namespace OAI


noncomputable section
namespace ExplicitCone
open Polynomial

lemma sectionCoefficient_mem_piece (i : Fin 6 × Fin 3) :
    sectionCoefficient i ∈ pieces 1 := by
  change IsIntegral polynomialAlgebra (monomial 1 (sectionCoefficient i))
  have hp : polynomialGenerator i ∈ polynomialAlgebra :=
    Algebra.subset_adjoin (Set.mem_range_self i)
  have hi := isIntegral_algebraMap (R := polynomialAlgebra) (A := L[X])
    (x := (⟨_,hp⟩ : polynomialAlgebra))
  change IsIntegral polynomialAlgebra (polynomialGenerator i) at hi
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simpa only [polynomialGenerator, pow_one] using hi

abbrev projBaseSection := SectionCompletion.linearSection pieces
  (sectionCoefficient (0,0)) (sectionCoefficient_mem_piece (0,0))
abbrev projBaseChart := SectionCompletion.homogeneousChart pieces
  (sectionCoefficient (0,0)) (sectionCoefficient_mem_piece (0,0))

/-- The actual degree-zero homogeneous localization in Proj of the WHOLE
normalized cone, not a surrogate affine model, is the literal smooth H-chart. -/
def projBaseChartEquiv : projBaseChart ≃ₐ[ℂ] sectionChart :=
  SectionCompletion.homogeneousChartAlgEquivOfAdjoin pieces (sectionCoefficient (0,0))
    (sectionCoefficient_mem_piece (0,0)) sectionCoefficient_base_ne_zero sectionCoefficient
    sectionCoefficient_mem_piece normalized_coefficient_mem_sectionChart

theorem projBaseChart_regular : IsRegularRing projBaseChart := by
  let := sectionChart_regular
  exact IsRegularRing.of_ringEquiv projBaseChartEquiv.symm.toRingEquiv

theorem projBaseChart_smooth : Algebra.Smooth ℂ projBaseChart := by
  let := sectionChart_smooth
  exact Algebra.Smooth.of_equiv projBaseChartEquiv.symm

lemma functionField_trdeg : Algebra.trdeg ℂ L = 2 := by
  have hK : Algebra.trdeg ℂ KummerLines.K = 2 := by
    rw [SmallCM.trdeg_fractionRing ℂ KummerLines.R KummerLines.K]
    simp [KummerLines.R, MvPolynomial.trdeg_of_isDomain]
  have h := trdeg_add_eq ℂ KummerLines.K (A := L)
  simpa only [hK, Cardinal.lift_ofNat, trdeg_eq_zero, add_zero] using h.symm

theorem sectionChart_dimension : ringKrullDim sectionChart = 2 := by
  apply SmallCM.dimension_of_trdeg ℂ sectionChart 2
  rw [← SmallCM.trdeg_fractionRing ℂ sectionChart L]
  exact functionField_trdeg

theorem projBaseChart_dimension : ringKrullDim projBaseChart = 2 :=
  projBaseChartEquiv.toRingEquiv.ringKrullDim.trans sectionChart_dimension

open AlgebraicGeometry CategoryTheory
/-- A genuine scheme isomorphism from the distinguished basic open of the
actual Proj of normalized coefficients to the explicit Kummer H-chart. -/
def projBaseOpenIso :
    (Proj.basicOpen (SectionCompletion.homogeneous pieces) projBaseSection).toScheme ≅
      Spec (CommRingCat.of sectionChart) :=
  (Proj.basicOpenIsoSpec (SectionCompletion.homogeneous pieces) projBaseSection
    (SectionCompletion.linearSection_homogeneous pieces _ _) (by norm_num : 0 < (1 : ℕ))) ≪≫
    (Scheme.Spec.mapIso (projBaseChartEquiv.symm.toRingEquiv.toCommRingCatIso).op)

end ExplicitCone


open nonZeroDivisors
namespace SmallCM

lemma finite_normalization_in_field_of_finite_type (k B F : Type*) [Field k] [CharZero k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Field F] [Algebra B F] [IsFractionRing B F] :
    Module.Finite B (integralClosure B F) := by
  obtain ⟨n, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let P := MvPolynomial (Fin n) k
  let : Algebra P B := f.toRingHom.toAlgebra
  let : Module.Finite P B := hfin
  let : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective P B).mpr hf
  let : Algebra P F := ((algebraMap B F).comp f.toRingHom).toAlgebra
  let : IsScalarTower P B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : FaithfulSMul P F := .trans P B F
  let : Algebra (FractionRing P) F := FractionRing.liftAlgebra P F
  let : IsScalarTower P (FractionRing P) F := FractionRing.isScalarTower_liftAlgebra P F
  let : Algebra.IsAlgebraic (FractionRing P) F :=
    isAlgebraic_of_isFractionRing P B (FractionRing P) F
  let : IsLocalization (Algebra.algebraMapSubmonoid B P⁰) F := by
    infer_instance
  let : FiniteDimensional (FractionRing P) F :=
    Module.Finite.of_isLocalization P B P⁰
  let C := integralClosure B F
  let : Algebra P C := (algebraMap B C).comp f.toRingHom |>.toAlgebra
  let : IsScalarTower P B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower P C F := IsScalarTower.to₁₃₄ P B C F
  let : IsIntegralClosure C P F :=
    ⟨IsIntegralClosure.algebraMap_injective C B _, fun {x} => by
      rw [← IsIntegralClosure.isIntegral_iff (A := C) (R := B)]
      exact ⟨fun h => h.tower_top, fun h => isIntegral_trans x h⟩⟩
  let : CharZero (FractionRing P) := inferInstance
  let : Module.Finite P C := IsIntegralClosure.finite P (FractionRing P) F C
  exact Module.Finite.of_restrictScalars_finite P B C

end SmallCM

namespace GradedNormalization
variable {k L : Type} [Field k] [CharZero k] [Field L] [Algebra k L]
open Polynomial
variable (B : Subalgebra k L[X]) [Algebra.FiniteType k B]
    [IsFractionRing B (RatFunc L)]

lemma finite_polynomial_normalization : Module.Finite B (integralClosure B L[X]) := by
  let N := integralClosure B L[X]
  let NF := integralClosure B (RatFunc L)
  let : Module.Finite B NF := SmallCM.finite_normalization_in_field_of_finite_type k B (RatFunc L)
  let : IsScalarTower N L[X] (RatFunc L) := inferInstance
  let : IsScalarTower B N (RatFunc L) := IsScalarTower.to₁₂₄ B N L[X] (RatFunc L)
  let : IsIntegralClosure N B (RatFunc L) :=
    IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn B N L[X] (RatFunc L)
  exact Module.Finite.equiv (IsIntegralClosure.equiv B NF (RatFunc L) N).toLinearEquiv

omit [CharZero k] [Algebra.FiniteType k B] [IsFractionRing B (RatFunc L)] in
lemma normal_polynomial_normalization : IsIntegrallyClosed (integralClosure B L[X]) :=
  IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
    (R := integralClosure B L[X]) (S := L[X])

end GradedNormalization

end


noncomputable section
namespace GradedNormalization
open Polynomial
variable {k L : Type} [Field k] [Field L] [Algebra k L]
variable {σ : Type} (v : σ → L) (d : σ → ℕ)

lemma monomial_algebra_scale (a : k) :
    ∀ p ∈ Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i))),
      scale a p ∈ Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i))) := by
  let B := Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i)))
  change B ≤ B.comap (scale a)
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  change scale a (monomial (d i) (v i)) ∈ B
  rw [scale_monomial]
  exact B.smul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) _

lemma positive_monomial_constantCoeff (hd : ∀ i, d i ≠ 0) :
    ∀ p ∈ Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i))),
      p.coeff 0 ∈ (⊥ : Subalgebra k L) := by
  let φ : L[X] →ₐ[k] L := (Polynomial.aeval (0 : L)).restrictScalars k
  have h : Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i))) ≤
      (⊥ : Subalgebra k L).comap φ := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change Polynomial.eval 0 (monomial (d i) (v i)) ∈ (⊥ : Subalgebra k L)
    simp [hd i]
  intro p hp
  have hh := h hp
  change Polynomial.eval 0 p ∈ (⊥ : Subalgebra k L) at hh
  rwa [← coeff_zero_eq_eval_zero] at hh
end GradedNormalization

namespace ExplicitCone
open Polynomial GradedNormalization

lemma polynomialGenerator_eq_monomial (i : Fin 6 × Fin 3) :
    polynomialGenerator i = monomial 1 (sectionCoefficient i) := by
  simp [polynomialGenerator, ← C_mul_X_pow_eq_monomial]

lemma polynomialAlgebra_scale (a : ℂ) :
    ∀ p ∈ polynomialAlgebra, scale a p ∈ polynomialAlgebra := by
  change ∀ p ∈ Algebra.adjoin ℂ (Set.range polynomialGenerator),
    scale a p ∈ Algebra.adjoin ℂ (Set.range polynomialGenerator)
  simp_rw [show polynomialGenerator = (fun i => monomial 1 (sectionCoefficient i)) from
    funext polynomialGenerator_eq_monomial]
  exact monomial_algebra_scale sectionCoefficient (fun _ => 1) a

lemma polynomialAlgebra_constantCoeff :
    ∀ p ∈ polynomialAlgebra, p.coeff 0 ∈ (⊥ : Subalgebra ℂ L) := by
  change ∀ p ∈ Algebra.adjoin ℂ (Set.range polynomialGenerator), _
  simp_rw [show polynomialGenerator = (fun i => monomial 1 (sectionCoefficient i)) from
    funext polynomialGenerator_eq_monomial]
  exact positive_monomial_constantCoeff sectionCoefficient (fun _ => 1) (fun _ => one_ne_zero)

end ExplicitCone
namespace GradedNormalization
open Polynomial
variable {k L : Type} [Field k] [CharZero k] [Field L] [Algebra k L]
variable (B : Subalgebra k L[X])

lemma polynomial_piece_eq (hB : ∀ a : k, ∀ p ∈ B, scale a p ∈ B) :
    SectionCompletion.polynomials (piece B) = (integralClosure B L[X]).restrictScalars k := by
  ext p
  change (∀ n, IsIntegral B (monomial n (p.coeff n))) ↔ IsIntegral B p
  constructor
  · intro h
    rw [p.as_sum_range]
    exact (integralClosure B L[X]).sum_mem (fun n _ => h n)
  · intro h n
    exact integral_monomial B hB h n

lemma polynomialPiece_finiteType [Algebra.FiniteType k B]
    [IsFractionRing B (RatFunc L)]
    (hB : ∀ a : k, ∀ p ∈ B, scale a p ∈ B) :
    Algebra.FiniteType k (SectionCompletion.polynomials (piece B)) := by
  rw [polynomial_piece_eq B hB]
  let : Module.Finite B (integralClosure B L[X]) := finite_polynomial_normalization B
  change Algebra.FiniteType k (integralClosure B L[X])
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k B)
    (inferInstance : Algebra.FiniteType B (integralClosure B L[X]))

lemma polynomialPiece_normalIn
    (hB : ∀ a : k, ∀ p ∈ B, scale a p ∈ B) :
    IsIntegrallyClosedIn (SectionCompletion.polynomials (piece B)) L[X] := by
  rw [polynomial_piece_eq B hB]
  change IsIntegrallyClosedIn (integralClosure B L[X]) L[X]
  infer_instance

end GradedNormalization

open AlgebraicGeometry CategoryTheory
private theorem proper_comp_iso {X Y Z : Scheme} (f : X ⟶ Y) (e : Y ≅ Z)
    [IsProper f] : IsProper (f ≫ e.hom) := by infer_instance

namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

lemma zero_piece : pieces 0 = LinearMap.range (Algebra.linearMap ℂ L) :=
  GradedNormalization.piece_zero polynomialAlgebra polynomialAlgebra_constantCoeff

instance completedRing_isLocalRing : IsLocalRing completedRing :=
  SectionCompletion.isLocalRing pieces (SectionCompletion.zero_piece_closed_inv pieces zero_piece)

instance normalizedPolynomialsFiniteType :
    Algebra.FiniteType ℂ (SectionCompletion.polynomials pieces) :=
  GradedNormalization.polynomialPiece_finiteType polynomialAlgebra polynomialAlgebra_scale

/-- Actual proper Proj of the entire normalized coefficient algebra. -/
abbrev projectiveSurface : Scheme := SectionCompletion.proj pieces

def degreeZeroEquiv : ℂ ≃ₐ[ℂ] SectionCompletion.homogeneous pieces 0 :=
  SectionCompletion.zeroEquiv pieces fun a ha => by
    rw [zero_piece] at ha
    exact ha

def degreeZeroSpecIso :
    Spec (CommRingCat.of (SectionCompletion.homogeneous pieces 0)) ≅
      Spec (CommRingCat.of ℂ) :=
  Scheme.Spec.mapIso degreeZeroEquiv.toRingEquiv.toCommRingCatIso.op

def projectiveSurfaceToComplex : projectiveSurface ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero (SectionCompletion.homogeneous pieces) ≫ degreeZeroSpecIso.hom

instance projectiveSurfaceProper : IsProper projectiveSurfaceToComplex :=
  (MorphismProperty.cancel_right_of_respectsIso @IsProper
    (Proj.toSpecZero (SectionCompletion.homogeneous pieces)) degreeZeroSpecIso.hom).mpr
      (SectionCompletion.projProper pieces)

end ExplicitCone

end


noncomputable section
namespace SectionChartSeries
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
variable (T : ℕ → Submodule k L) [SetLike.GradedMonoid T]
variable (A : Subalgebra k L) (c : L)
variable (h : ∀ n a, a ∈ T n → a / c ^ n ∈ A)

def localSeries (f : SectionCompletion.series T) : PowerSeries A :=
  PowerSeries.mk fun n => ⟨PowerSeries.coeff n f.val / c ^ n, h n _ (f.property n)⟩

lemma map_localSeries (f : SectionCompletion.series T) :
    PowerSeries.map A.val.toRingHom (localSeries T A c h f) =
      PowerSeries.rescale c⁻¹ f.val := by
  ext n
  simp only [localSeries, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    PowerSeries.coeff_rescale, inv_pow, div_eq_mul_inv, mul_comm]
  rfl

def hom : SectionCompletion.series T →ₐ[k] PowerSeries A where
  toFun := localSeries T A c h
  map_zero' := by
    apply PowerSeries.map_injective A.val.toRingHom Subtype.val_injective
    rw [map_localSeries, map_zero]
    exact map_zero _
  map_one' := by
    apply PowerSeries.map_injective A.val.toRingHom Subtype.val_injective
    rw [map_localSeries, map_one]
    exact map_one _
  map_add' f g := by
    apply PowerSeries.map_injective A.val.toRingHom Subtype.val_injective
    rw [map_localSeries, map_add, map_localSeries, map_localSeries]
    exact map_add _ _ _
  map_mul' f g := by
    apply PowerSeries.map_injective A.val.toRingHom Subtype.val_injective
    rw [map_localSeries, map_mul, map_localSeries, map_localSeries]
    exact map_mul _ _ _
  commutes' a := by
    apply PowerSeries.map_injective A.val.toRingHom Subtype.val_injective
    rw [map_localSeries]
    change PowerSeries.rescale c⁻¹ (algebraMap k (PowerSeries L) a) =
      PowerSeries.map A.val.toRingHom (algebraMap k (PowerSeries A) a)
    ext n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_map,
      PowerSeries.algebraMap_apply, PowerSeries.coeff_C]
    by_cases hn : n = 0
    · subst n; simp
    · simp [hn]


lemma hom_injective (hc : c ≠ 0) : Function.Injective (hom T A c h) := by
  intro f g hfg
  apply Subtype.ext
  apply PowerSeries.rescale_injective (inv_ne_zero hc)
  rw [← map_localSeries T A c h f, ← map_localSeries T A c h g]
  exact congrArg (PowerSeries.map A.val.toRingHom) hfg

lemma coeff_hom (f : SectionCompletion.series T) (n : ℕ) :
    ((PowerSeries.coeff n (hom T A c h f) : A) : L) = PowerSeries.coeff n f.val / c ^ n := by
  simp [hom, localSeries]

end SectionChartSeries


namespace SectionGenerated
open scoped BigOperators
variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Fintype σ]
variable (v : σ → K) (d : σ → ℕ)

noncomputable def genSeries (i : σ) : PowerSeries K := PowerSeries.C (v i) * PowerSeries.X ^ d i

lemma hasSubst (hd : ∀ i, d i ≠ 0) : MvPowerSeries.HasSubst (genSeries v d) where
  const_coeff i := by
    change IsNilpotent (PowerSeries.constantCoeff (genSeries v d i))
    simp [genSeries, hd i]
  coeff_zero _ := Set.toFinite _

omit [Fintype σ] in
lemma monomial_subst (e : σ →₀ ℕ) :
    e.prod (fun i n => (genSeries v d i)^n) =
      PowerSeries.C (e.prod (fun i n => v i^n)) * PowerSeries.X^(Finsupp.weight d e) := by
  classical
  simp only [genSeries, mul_pow, ← map_pow, Finsupp.prod, Finset.prod_mul_distrib,
    ← map_prod, ← pow_mul, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum,
    smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

lemma coeff_subst (hd : ∀ i, d i ≠ 0) (f : MvPowerSeries σ k) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.subst (genSeries v d) f) =
      ∑ᶠ e : σ →₀ ℕ, if Finsupp.weight d e = n then
        MvPowerSeries.coeff e f • e.prod (fun i j => v i ^ j) else 0 := by
  classical
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst (hasSubst v d hd)]
  apply finsum_congr
  intro e
  rw [monomial_subst]
  change MvPowerSeries.coeff e f •
    PowerSeries.coeff n (PowerSeries.C _ * PowerSeries.X ^ _) = _
  rw [PowerSeries.coeff_C_mul_X_pow]
  split_ifs <;> simp_all
end SectionGenerated
namespace SectionGenerated
open scoped BigOperators
variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Fintype σ]
variable (v : σ → K) (d : σ → ℕ)

lemma coeff_subst_fiber (hd : ∀ i, d i ≠ 0) (f : MvPowerSeries σ k) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.subst (genSeries v d) f) =
      ∑ᶠ e : {e : σ →₀ ℕ // Finsupp.weight d e = n},
        MvPowerSeries.coeff e.val f • e.val.prod (fun i j => v i ^ j) := by
  rw [coeff_subst v d hd]
  simpa only [finsum_eq_if] using (finsum_subtype_eq_finsum_cond
    (f := fun e : σ →₀ ℕ => MvPowerSeries.coeff e f • e.prod (fun i j => v i ^ j))
    (fun e => Finsupp.weight d e = n)).symm

lemma exists_subst_of_coeff_span (hd : ∀ i, d i ≠ 0) (p : PowerSeries K)
    (hp : ∀ n, PowerSeries.coeff n p ∈ Submodule.span k
      (Set.range (fun e : {e : σ →₀ ℕ // Finsupp.weight d e = n} =>
        e.val.prod (fun i j => v i ^ j)))) :
    ∃ f : MvPowerSeries σ k, MvPowerSeries.subst (genSeries v d) f = p := by
  classical
  have hc := fun n => Finsupp.mem_span_range_iff_exists_finsupp.mp (hp n)
  choose c hc using hc
  let f : MvPowerSeries σ k := fun e => c (Finsupp.weight d e) ⟨e, rfl⟩
  refine ⟨f, PowerSeries.ext fun n => ?_⟩
  rw [coeff_subst_fiber v d hd]
  calc
    _ = ∑ᶠ e : {e : σ →₀ ℕ // Finsupp.weight d e = n},
        c n e • e.val.prod (fun i j => v i ^ j) := by
      apply finsum_congr
      intro e
      congr 1
      change c (Finsupp.weight d e.val) ⟨e.val, rfl⟩ = c n e
      rcases e with ⟨e, he⟩
      cases he
      rfl
    _ = (c n).sum (fun e a => a • e.val.prod (fun i j => v i ^ j)) := by
      apply finsum_eq_sum_of_support_subset
      intro e he
      exact Finsupp.mem_support_iff.mpr (fun hz => he (by simp [hz]))
    _ = _ := hc n
end SectionGenerated
namespace SectionGenerated
open scoped BigOperators
variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Fintype σ]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (v : σ → K) (d : σ → ℕ)

lemma subst_mem (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i))
    (f : MvPowerSeries σ k) : MvPowerSeries.subst (genSeries v d) f ∈ SectionCompletion.series T := by
  classical
  intro n
  rw [coeff_subst_fiber v d hd]
  let : Fintype {e : σ →₀ ℕ // Finsupp.weight d e = n} :=
    (Finsupp.finite_of_nat_weight_eq d hd n).fintype
  rw [finsum_eq_sum_of_fintype]
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  have h := SetLike.prod_pow_mem_graded T d v (fun i => e.val i)
    (F := e.val.support) (fun i _ => hv i)
  have he : (∑ i ∈ e.val.support, e.val i • d i) = n := by
    simpa only [Finsupp.weight_apply, Finsupp.sum] using e.property
  rw [he] at h
  exact h

noncomputable def substHom (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i)) :
    MvPowerSeries σ k →ₐ[k] SectionCompletion.series T :=
  (MvPowerSeries.substAlgHom (R := k) (hasSubst v d hd)).codRestrict
    (SectionCompletion.series T) (fun f => by
      simpa only [MvPowerSeries.substAlgHom_apply] using subst_mem T v d hd hv f)

lemma substHom_surjective (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i))
    (hgen : ∀ n, T n = Submodule.span k
      (Set.range (fun e : {e : σ →₀ ℕ // Finsupp.weight d e = n} =>
        e.val.prod (fun i j => v i ^ j)))) :
    Function.Surjective (substHom T v d hd hv) := by
  intro p
  obtain ⟨f, hf⟩ := exists_subst_of_coeff_span v d hd p.val (fun n => by
    rw [← hgen n]
    exact p.property n)
  refine ⟨f, Subtype.ext ?_⟩
  change (MvPowerSeries.substAlgHom (R := k) (hasSubst v d hd)) f = p.val
  simpa only [MvPowerSeries.substAlgHom_apply] using hf

lemma isNoetherianRing (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i))
    (hgen : ∀ n, T n = Submodule.span k
      (Set.range (fun e : {e : σ →₀ ℕ // Finsupp.weight d e = n} =>
        e.val.prod (fun i j => v i ^ j)))) :
    IsNoetherianRing (SectionCompletion.series T) :=
  isNoetherianRing_of_surjective _ _ (substHom T v d hd hv).toRingHom
    (substHom_surjective T v d hd hv hgen)
end SectionGenerated


lemma precomplete_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) (hf : Function.Surjective f) [IsPrecomplete I R] :
    IsPrecomplete (I.map f) S := by
  let : Algebra R S := f.toAlgebra
  change IsPrecomplete (I.map (algebraMap R S)) S
  rw [IsPrecomplete.map_algebraMap_iff]
  apply AdicCompletion.of_surjective_iff.mp
  intro x
  obtain ⟨y, hy⟩ := AdicCompletion.map_surjective I (f := Algebra.linearMap R S) hf x
  obtain ⟨a, ha⟩ := AdicCompletion.of_surjective I R y
  refine ⟨f a, ?_⟩
  rw [← hy, ← ha]
  rw [AdicCompletion.map_of]
  rfl

lemma complete_local_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  have h := precomplete_of_surjective (IsLocalRing.maximalIdeal R) f hf
  rw [IsLocalRing.map_maximalIdeal_of_surjective f hf] at h
  exact { toIsPrecomplete := h, toIsHausdorff := inferInstance }

open IsLocalRing
open scoped BigOperators

lemma mvPowerSeries_constantCoeff_zero_mem_vars
    {σ K : Type*} [Fintype σ] [CommRing K] (f : MvPowerSeries σ K)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)) := by
  classical
  let p : σ → MvPowerSeries σ K := fun i d =>
    if h : d ≠ 0 then if i = (Finsupp.ne_iff.mp h).choose then f d else 0 else 0
  have hp : ∀ i, MvPowerSeries.X i ∣ p i := by
    intro i
    apply MvPowerSeries.X_dvd_iff.mpr
    intro d hdi
    change (if h : d ≠ 0 then if i = (Finsupp.ne_iff.mp h).choose then f d else 0 else 0) = 0
    split_ifs with hd hi
    · have hne := (Finsupp.ne_iff.mp hd).choose_spec
      rw [← hi] at hne
      exact (hne hdi).elim
    · rfl
    · rfl
  have hsum : f = ∑ i, p i := by
    apply MvPowerSeries.ext
    intro d
    rw [map_sum]
    change f d = ∑ i, p i d
    by_cases hd : d = 0
    · subst d
      change f 0 = 0 at hf
      simpa [p] using hf
    · simp [p, hd]
  rw [hsum]
  apply Ideal.sum_mem
  intro i _
  obtain ⟨g, hg⟩ := hp i
  rw [hg]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))

lemma mvPowerSeries_vars_eq_maximal
    {σ K : Type*} [Fintype σ] [Field K] :
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)) =
      maximalIdeal (MvPowerSeries σ K) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries σ K)
    rw [mem_maximalIdeal]
    change ¬ IsUnit (MvPowerSeries.X i : MvPowerSeries σ K)
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  · intro f hf
    apply mvPowerSeries_constantCoeff_zero_mem_vars
    rw [mem_maximalIdeal] at hf
    change ¬ IsUnit f at hf
    rwa [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not] at hf

namespace SectionGenerated
open scoped BigOperators
variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Fintype σ]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (v : σ → K) (d : σ → ℕ)

lemma adicComplete [IsLocalRing (SectionCompletion.series T)]
    (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i))
    (hgen : ∀ n, T n = Submodule.span k
      (Set.range (fun e : {e : σ →₀ ℕ // Finsupp.weight d e = n} =>
        e.val.prod (fun i j => v i ^ j)))) :
    IsAdicComplete (IsLocalRing.maximalIdeal (SectionCompletion.series T))
      (SectionCompletion.series T) := by
  let := isNoetherianRing T v d hd hv hgen
  have : IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ k)) (MvPowerSeries σ k) := by
    rw [← mvPowerSeries_vars_eq_maximal]
    infer_instance
  exact complete_local_of_surjective (substHom T v d hd hv).toRingHom
    (substHom_surjective T v d hd hv hgen)
end SectionGenerated

end


noncomputable section
open Polynomial
open scoped BigOperators
namespace HomogeneousGeneration
variable {k L : Type} [Field k] [Field L] [Algebra k L]

lemma exists_positive_generators (A : Subalgebra k L[X]) [Algebra.FiniteType k A]
    (hA : ∀ p ∈ A, ∀ n, monomial n (p.coeff n) ∈ A)
    (hzero : ∀ p ∈ A, p.coeff 0 ∈ (⊥ : Subalgebra k L)) :
    ∃ (σ : Type) (_ : Fintype σ) (v : σ → L) (d : σ → ℕ),
      (∀ i, d i ≠ 0) ∧
      A = Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i))) := by
  classical
  obtain ⟨s, hs⟩ := (Subalgebra.fg_iff_finiteType A).mpr inferInstance
  let σ := Σ p : (s : Set L[X]), Fin p.val.natDegree
  let v : σ → L := fun i => i.1.val.coeff (i.2.val + 1)
  let d : σ → ℕ := fun i => i.2.val + 1
  refine ⟨σ, inferInstance, v, d, fun i => by simp [d], ?_⟩
  let B := Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i)))
  apply le_antisymm
  · rw [← hs]
    apply Algebra.adjoin_le
    intro p hp
    rw [p.as_sum_range]
    apply B.sum_mem
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      rw [monomial_zero_left]
      obtain ⟨a, ha⟩ := hzero p (hs ▸ Algebra.subset_adjoin hp)
      rw [← ha]
      exact B.algebraMap_mem a
    · apply Algebra.subset_adjoin
      refine ⟨⟨⟨p, hp⟩, ⟨n-1, ?_⟩⟩, ?_⟩
      · change n-1 < p.natDegree
        have := Finset.mem_range.mp hn
        omega
      · change monomial (n-1+1) (p.coeff (n-1+1)) = monomial n (p.coeff n)
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hA i.1.val (hs ▸ Algebra.subset_adjoin i.1.property) _

/-- Multiplicative homogeneous monomials describing every degree-n coefficient. -/
def spanPiece {σ : Type} (v : σ → L) (d : σ → ℕ) (n : ℕ) : Submodule k L :=
  Submodule.span k (Set.range (fun e : {e : σ →₀ ℕ // Finsupp.weight d e = n} =>
    e.val.prod (fun i j => v i ^ j)))

lemma monomial_prod {σ : Type} (v : σ → L) (d : σ → ℕ) (e : σ →₀ ℕ) :
    e.prod (fun i j => (monomial (d i) (v i) : L[X]) ^ j) =
      monomial (Finsupp.weight d e) (e.prod (fun i j => v i ^ j)) := by
  classical
  simp only [← C_mul_X_pow_eq_monomial, mul_pow, ← map_pow, Finsupp.prod,
    Finset.prod_mul_distrib, ← map_prod, ← pow_mul, Finset.prod_pow_eq_pow_sum,
    Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

lemma coeff_mem_span {σ : Type} (v : σ → L) (d : σ → ℕ)
    {p : L[X]} (hp : p ∈ Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i))))
    (n : ℕ) : p.coeff n ∈ spanPiece (k := k) v d n := by
  classical
  rw [Algebra.adjoin_range_eq_range_aeval] at hp
  obtain ⟨q, rfl⟩ := hp
  rw [MvPolynomial.as_sum q, map_sum, finsetSum_coeff]
  apply Submodule.sum_mem
  intro e _
  change ((MvPolynomial.aeval (fun i => monomial (d i) (v i)))
    (MvPolynomial.monomial e (q.coeff e))).coeff n ∈ _
  rw [MvPolynomial.aeval_monomial, monomial_prod]
  rw [Polynomial.algebraMap_apply, coeff_C_mul, coeff_monomial]
  split_ifs with he
  · subst n
    simpa only [Algebra.smul_def] using (spanPiece (k := k) v d _).smul_mem (q.coeff e) (Submodule.subset_span ⟨⟨e, rfl⟩, rfl⟩)
  · simp

end HomogeneousGeneration

namespace HomogeneousGeneration
open Polynomial
variable {k L : Type} [Field k] [Field L] [Algebra k L]

lemma piece_eq_span {σ : Type} (v : σ → L) (d : σ → ℕ)
    (T : ℕ → Submodule k L) (A : Subalgebra k L[X])
    (hA : A = Algebra.adjoin k (Set.range (fun i => monomial (d i) (v i))))
    (hT : ∀ n c, c ∈ T n ↔ monomial n c ∈ A) (n : ℕ) :
    T n = spanPiece v d n := by
  classical
  apply le_antisymm
  · intro c hc
    have h := (hT n c).mp hc
    rw [hA] at h
    simpa using coeff_mem_span v d h n
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨e, he⟩, rfl⟩
    apply (hT n _).mpr
    change monomial n (e.prod (fun i j => v i ^ j)) ∈ A
    rw [← he, ← monomial_prod]
    apply A.prod_mem
    intro i _
    apply A.pow_mem
    rw [hA]
    exact Algebra.subset_adjoin ⟨i, rfl⟩

end HomogeneousGeneration

end


noncomputable section
namespace SectionCompletion
open Polynomial
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma finite_positive_presentation [Algebra.FiniteType k (polynomials T)]
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K)) :
    ∃ (σ : Type) (_ : Fintype σ) (v : σ → K) (d : σ → ℕ),
      (∀ i, d i ≠ 0) ∧ (∀ i, v i ∈ T (d i)) ∧
      ∀ n, T n = Submodule.span k
        (Set.range (fun e : {e : σ →₀ ℕ // Finsupp.weight d e = n} =>
          e.val.prod (fun i j => v i ^ j))) := by
  have hh : ∀ p ∈ polynomials T, ∀ n,
      Polynomial.monomial n (p.coeff n) ∈ polynomials T := by
    intro p hp n
    exact (monomial_mem_polynomials T n _).mpr (hp n)
  have hz : ∀ p ∈ polynomials T, p.coeff 0 ∈ (⊥ : Subalgebra k K) := by
    intro p hp
    have hc := hp 0
    rw [hzero, LinearMap.mem_range] at hc
    obtain ⟨a, ha⟩ := hc
    exact ⟨a, ha⟩
  obtain ⟨σ, hσ, v, d, hd, hA⟩ :=
    HomogeneousGeneration.exists_positive_generators (polynomials T) hh hz
  let := hσ
  refine ⟨σ, hσ, v, d, hd, ?_, ?_⟩
  · intro i
    apply (monomial_mem_polynomials T _ _).mp
    rw [hA]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  · intro n
    exact HomogeneousGeneration.piece_eq_span v d T (polynomials T) hA
      (fun n c => (monomial_mem_polynomials T n c).symm) n


end SectionCompletion


namespace CompletedCartierChart
variable {k L : Type} [Field k] [Field L] [Algebra k L]
variable (T : ℕ → Submodule k L) [SetLike.GradedMonoid T]
variable (A : Subalgebra k L) (c : L)
variable (h : ∀ n a, a ∈ T n → a / c ^ n ∈ A)

abbrev seriesMap := SectionChartSeries.hom T A c h
abbrev constants : A →ₐ[k] PowerSeries A := IsScalarTower.toAlgHom k A (PowerSeries A)

def chart : Subalgebra k (PowerSeries A) :=
  (seriesMap T A c h).range ⊔ (constants A).range

def sourceHom : SectionCompletion.series T →ₐ[k] chart T A c h :=
  (seriesMap T A c h).codRestrict _ fun _ => (show (seriesMap T A c h).range ≤ chart T A c h from le_sup_left)
    (AlgHom.mem_range_self _ _)

def constantHom : A →ₐ[k] chart T A c h :=
  (constants A).codRestrict _ fun _ => (show (constants A).range ≤ chart T A c h from le_sup_right)
    (AlgHom.mem_range_self _ _)

def evaluation : chart T A c h →ₐ[k] A where
  toRingHom := PowerSeries.constantCoeff.comp (chart T A c h).val.toRingHom
  commutes' a := by simp [PowerSeries.algebraMap_apply]

@[simp] lemma evaluation_constant (a : A) :
    evaluation T A c h (constantHom T A c h a) = a := by
  change PowerSeries.constantCoeff (PowerSeries.C a) = a
  simp

lemma evaluation_surjective : Function.Surjective (evaluation T A c h) :=
  fun a => ⟨constantHom T A c h a, evaluation_constant T A c h a⟩

lemma variable_mem (hc : c ∈ T 1) (hc0 : c ≠ 0) :
    (PowerSeries.X : PowerSeries A) ∈ chart T A c h := by
  let p : SectionCompletion.series T := ⟨PowerSeries.monomial 1 c, by
    intro n; by_cases hn : n = 1
    · subst n; simpa using hc
    · simp [PowerSeries.coeff_monomial, hn]⟩
  have hp : seriesMap T A c h p = PowerSeries.X := by
    ext n
    rw [SectionChartSeries.coeff_hom]
    change PowerSeries.coeff n (PowerSeries.monomial 1 c) / c ^ n =
      ((PowerSeries.coeff n (PowerSeries.X : PowerSeries A) : A) : L)
    by_cases hn : n = 1
    · subst n; simp [hc0]
    · simp [PowerSeries.coeff_monomial, PowerSeries.coeff_X, hn]
  rw [← hp]
  exact (show (seriesMap T A c h).range ≤ chart T A c h from le_sup_left)
    (AlgHom.mem_range_self _ _)

def parameter (hc : c ∈ T 1) (hc0 : c ≠ 0) : chart T A c h :=
  ⟨PowerSeries.X, variable_mem T A c h hc hc0⟩

lemma parameter_ne_zero (hc : c ∈ T 1) (hc0 : c ≠ 0) :
    parameter T A c h hc hc0 ≠ 0 := by
  intro he
  have hh := congrArg Subtype.val he
  exact PowerSeries.X_ne_zero hh

@[simp] lemma evaluation_parameter (hc : c ∈ T 1) (hc0 : c ≠ 0) :
    evaluation T A c h (parameter T A c h hc hc0) = 0 := by
  change PowerSeries.constantCoeff PowerSeries.X = 0
  simp

lemma span_parameter_le_ker (hc : c ∈ T 1) (hc0 : c ≠ 0) :
    Ideal.span {parameter T A c h hc hc0} ≤ RingHom.ker (evaluation T A c h) := by
  apply Ideal.span_le.mpr
  rintro _ rfl
  exact evaluation_parameter T A c h hc hc0

lemma source_generator {σ : Type} [Fintype σ] (v : σ → L) (d : σ → ℕ)
    (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i))
    (hc : c ∈ T 1) (hc0 : c ≠ 0) (i : σ) :
    sourceHom T A c h (SectionGenerated.substHom T v d hd hv (MvPowerSeries.X i)) =
      constantHom T A c h ⟨v i / c ^ d i, h _ _ (hv i)⟩ *
        parameter T A c h hc hc0 ^ d i := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  apply Subtype.ext
  change ((PowerSeries.coeff n (seriesMap T A c h
      (SectionGenerated.substHom T v d hd hv (MvPowerSeries.X i))) : A) : L) = _
  rw [SectionChartSeries.coeff_hom]
  have hs : (SectionGenerated.substHom T v d hd hv
      (MvPowerSeries.X i : MvPowerSeries σ k)).val = SectionGenerated.genSeries v d i := by
    change MvPowerSeries.substAlgHom (R := k) (SectionGenerated.hasSubst v d hd)
      (MvPowerSeries.X i) = _
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X (SectionGenerated.hasSubst v d hd)]
  rw [hs]
  change PowerSeries.coeff n (SectionGenerated.genSeries v d i) / c ^ n =
    ((PowerSeries.coeff n (PowerSeries.C (⟨v i / c ^ d i, h _ _ (hv i)⟩ : A) *
      PowerSeries.X ^ d i) : A) : L)
  simp only [SectionGenerated.genSeries, PowerSeries.coeff_C_mul_X_pow]
  by_cases hn : n = d i
  · subst n; simp
  · simp [hn]

lemma source_generator_mem_span {σ : Type} [Fintype σ] (v : σ → L) (d : σ → ℕ)
    (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i))
    (hc : c ∈ T 1) (hc0 : c ≠ 0) (i : σ) :
    sourceHom T A c h (SectionGenerated.substHom T v d hd hv (MvPowerSeries.X i)) ∈
      Ideal.span {parameter T A c h hc hc0} := by
  rw [source_generator]
  apply Ideal.mul_mem_left
  exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _
    (Nat.pos_of_ne_zero (hd i))

lemma source_sub_constant_mem_span_of_generators {σ : Type} [Fintype σ]
    (v : σ → L) (d : σ → ℕ) (hd : ∀ i, d i ≠ 0) (hv : ∀ i, v i ∈ T (d i))
    (hg : ∀ n, T n = HomogeneousGeneration.spanPiece v d n)
    (hc : c ∈ T 1) (hc0 : c ≠ 0) (f : SectionCompletion.series T) :
    sourceHom T A c h f -
      constantHom T A c h (evaluation T A c h (sourceHom T A c h f)) ∈
        Ideal.span {parameter T A c h hc hc0} := by
  let ψ := (sourceHom T A c h).comp (SectionGenerated.substHom T v d hd hv)
  let I : Ideal (chart T A c h) := Ideal.span {parameter T A c h hc hc0}
  have hvars : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ≤
      I.comap ψ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact source_generator_mem_span T A c h v d hd hv hc hc0 i
  obtain ⟨g,rfl⟩ := SectionGenerated.substHom_surjective T v d hd hv hg f
  have hzero : MvPowerSeries.constantCoeff (g - MvPowerSeries.C
      (MvPowerSeries.constantCoeff g)) = 0 := by simp
  have hm := hvars (mvPowerSeries_constantCoeff_zero_mem_vars _ hzero)
  change ψ (g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) ∈ I at hm
  have hcst : ψ (MvPowerSeries.C (MvPowerSeries.constantCoeff g)) =
      algebraMap k (chart T A c h) (MvPowerSeries.constantCoeff g) := ψ.commutes _
  rw [map_sub, hcst] at hm
  have he := span_parameter_le_ker T A c h hc hc0 hm
  change evaluation T A c h (ψ g -
    algebraMap k (chart T A c h) (MvPowerSeries.constantCoeff g)) = 0 at he
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at he
  change ψ g - constantHom T A c h (evaluation T A c h (ψ g)) ∈ I
  rw [he, AlgHom.commutes]
  exact hm

lemma source_sub_constant_mem_span [Algebra.FiniteType k (SectionCompletion.polynomials T)]
    (hz : T 0 = LinearMap.range (Algebra.linearMap k L))
    (hc : c ∈ T 1) (hc0 : c ≠ 0) (f : SectionCompletion.series T) :
    sourceHom T A c h f -
      constantHom T A c h (evaluation T A c h (sourceHom T A c h f)) ∈
        Ideal.span {parameter T A c h hc hc0} := by
  obtain ⟨σ,hσ,v,d,hd,hv,hg⟩ := SectionCompletion.finite_positive_presentation T hz
  let := hσ
  exact source_sub_constant_mem_span_of_generators T A c h v d hd hv hg hc hc0 f

lemma generators_sup_top :
    (sourceHom T A c h).range ⊔ (constantHom T A c h).range = ⊤ := by
  apply Subalgebra.map_injective (f := (chart T A c h).val) Subtype.val_injective
  rw [Algebra.map_sup, Algebra.map_top, Subalgebra.range_val,
    ← AlgHom.range_comp, ← AlgHom.range_comp]
  rfl

lemma sub_constant_mem_span [Algebra.FiniteType k (SectionCompletion.polynomials T)]
    (hz : T 0 = LinearMap.range (Algebra.linearMap k L))
    (hc : c ∈ T 1) (hc0 : c ≠ 0) (b : chart T A c h) :
    b - constantHom T A c h (evaluation T A c h b) ∈
      Ideal.span {parameter T A c h hc hc0} := by
  let I : Ideal (chart T A c h) := Ideal.span {parameter T A c h hc hc0}
  let q := Ideal.Quotient.mkₐ k I
  have he : q = (q.comp (constantHom T A c h)).comp (evaluation T A c h) := by
    apply AlgHom.equalizer_eq_top.mp
    apply top_unique
    rw [← generators_sup_top T A c h]
    apply sup_le
    · rintro _ ⟨f,rfl⟩
      apply Ideal.Quotient.eq.mpr
      exact source_sub_constant_mem_span T A c h hz hc hc0 f
    · rintro _ ⟨a,rfl⟩
      change q (constantHom T A c h a) =
        q (constantHom T A c h (evaluation T A c h (constantHom T A c h a)))
      rw [evaluation_constant]
  exact Ideal.Quotient.eq.mp (DFunLike.congr_fun he b)

lemma ker_evaluation [Algebra.FiniteType k (SectionCompletion.polynomials T)]
    (hz : T 0 = LinearMap.range (Algebra.linearMap k L))
    (hc : c ∈ T 1) (hc0 : c ≠ 0) :
    RingHom.ker (evaluation T A c h) = Ideal.span {parameter T A c h hc hc0} := by
  apply le_antisymm
  · intro b hb
    have he : evaluation T A c h b = 0 := hb
    have hh := sub_constant_mem_span T A c h hz hc hc0 b
    simpa only [he, map_zero, sub_zero] using hh
  · exact span_parameter_le_ker T A c h hc hc0

noncomputable def exceptionalEquiv
    [Algebra.FiniteType k (SectionCompletion.polynomials T)]
    (hz : T 0 = LinearMap.range (Algebra.linearMap k L))
    (hc : c ∈ T 1) (hc0 : c ≠ 0) :
    (chart T A c h ⧸ Ideal.span {parameter T A c h hc hc0}) ≃ₐ[k] A :=
  (Ideal.quotientEquivAlgOfEq k (ker_evaluation T A c h hz hc hc0).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (evaluation_surjective T A c h))

end CompletedCartierChart

namespace ExplicitCone

lemma actualCompletion_noetherian : IsNoetherianRing completedRing := by
  obtain ⟨σ,hσ,v,d,hd,hv,hg⟩ := SectionCompletion.finite_positive_presentation pieces zero_piece
  let := hσ
  exact SectionGenerated.isNoetherianRing pieces v d hd hv hg

end ExplicitCone


end

end OAI
