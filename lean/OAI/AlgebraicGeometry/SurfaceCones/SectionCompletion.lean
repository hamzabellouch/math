import OAI.AlgebraicGeometry.SurfaceCones.KummerSectionAffineOpen

namespace OAI


/-! The coefficient description of the completed section ring after a rational
trivialization of the polarization, as in OpenAI's
*A Complete Local Domain without a Small Cohen–Macaulay Module*, Section 2. -/
namespace SectionCompletion
open scoped BigOperators

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

/-- The product of the graded pieces with graded Cauchy multiplication. -/
def series : Subalgebra k (PowerSeries K) where
  carrier := {f | ∀ n, PowerSeries.coeff n f ∈ T n}
  zero_mem' := by intro n; simp
  add_mem' := by intro f g hf hg n; simpa using (T n).add_mem (hf n) (hg n)
  one_mem' := by
    intro n
    by_cases hn : n = 0
    · subst n; simpa using SetLike.one_mem_graded T
    · simp [PowerSeries.coeff_one, hn]
  mul_mem' := by
    intro f g hf hg n
    rw [PowerSeries.coeff_mul]
    apply Submodule.sum_mem
    intro p hp
    have hpn := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    simpa [hpn] using SetLike.mul_mem_graded (hf p.1) (hg p.2)
  algebraMap_mem' := by
    intro a n
    rw [PowerSeries.algebraMap_apply]
    rw [PowerSeries.coeff_C]
    split_ifs with hn
    · subst n
      simpa [Algebra.smul_def] using (T 0).smul_mem a (SetLike.one_mem_graded T)
    · exact (T n).zero_mem

lemma inverse_mem (hz : ∀ a ∈ T 0, a⁻¹ ∈ T 0) (f : series T) :
    (f.val)⁻¹ ∈ series T := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · subst n
      exact hz _ (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using f.property 0)
    · have ha : -(PowerSeries.constantCoeff f.val)⁻¹ ∈ T 0 :=
        (T 0).neg_mem (hz _ (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using f.property 0))
      have hb : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        if p.2 < n then PowerSeries.coeff p.1 f.val *
          PowerSeries.coeff p.2 f.val⁻¹ else 0) ∈ T n := by
        apply Submodule.sum_mem
        intro p hp
        split_ifs with hp2
        · have hpn := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          simpa [hpn] using SetLike.mul_mem_graded (f.property p.1) (ih p.2 hp2)
        · exact (T n).zero_mem
      simpa only [zero_add] using SetLike.mul_mem_graded ha hb

lemma isUnit_iff_constant_ne_zero (hz : ∀ a ∈ T 0, a⁻¹ ∈ T 0) (f : series T) :
    IsUnit f ↔ PowerSeries.constantCoeff f.val ≠ 0 := by
  constructor
  · intro h
    exact isUnit_iff_ne_zero.mp (h.map ((PowerSeries.constantCoeff).comp (series T).val.toRingHom))
  · intro h
    refine ⟨⟨f, ⟨f.val⁻¹, inverse_mem T hz f⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      exact PowerSeries.mul_inv_cancel f.val h
    · apply Subtype.ext
      exact PowerSeries.inv_mul_cancel f.val h

lemma isLocalRing (hz : ∀ a ∈ T 0, a⁻¹ ∈ T 0) : IsLocalRing (series T) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  by_cases hf : PowerSeries.constantCoeff f.val = 0
  · right
    apply (isUnit_iff_constant_ne_zero T hz _).mpr
    change PowerSeries.constantCoeff (1 - f.val) ≠ 0
    simp [hf]
  · exact Or.inl ((isUnit_iff_constant_ne_zero T hz f).mpr hf)

omit [SetLike.GradedMonoid T] in
lemma zero_piece_closed_inv (hzero : T 0 = LinearMap.range (Algebra.linearMap k K)) :
    ∀ a ∈ T 0, a⁻¹ ∈ T 0 := by
  intro a ha
  rw [hzero, LinearMap.mem_range] at ha ⊢
  obtain ⟨b, rfl⟩ := ha
  exact ⟨b⁻¹, map_inv₀ (algebraMap k K) b⟩

lemma maximal_mem_iff (hzero : T 0 = LinearMap.range (Algebra.linearMap k K))
    [IsLocalRing (series T)] (f : series T) :
    f ∈ IsLocalRing.maximalIdeal (series T) ↔ PowerSeries.constantCoeff f.val = 0 := by
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit f ↔ _
  rw [isUnit_iff_constant_ne_zero T (zero_piece_closed_inv T hzero), not_not]

lemma residue_bijective (hzero : T 0 = LinearMap.range (Algebra.linearMap k K))
    [IsLocalRing (series T)] :
    Function.Bijective (algebraMap k (IsLocalRing.ResidueField (series T))) := by
  refine ⟨(algebraMap k _).injective, ?_⟩
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hf := f.property 0
  rw [hzero, LinearMap.mem_range] at hf
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, ?_⟩
  change Ideal.Quotient.mk _ (algebraMap k (series T) a) = Ideal.Quotient.mk _ f
  apply Ideal.Quotient.eq.mpr
  rw [maximal_mem_iff T hzero]
  change PowerSeries.constantCoeff (PowerSeries.C (algebraMap k K a) - f.val) = 0
  simpa only [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero, Algebra.linearMap_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] using ha

end SectionCompletion


noncomputable section

namespace ExplicitCone
open Polynomial
def polynomialGenerator (i : Fin 6 × Fin 3) : L[X] := C (sectionCoefficient i) * X
abbrev polynomialAlgebra := Algebra.adjoin ℂ (Set.range polynomialGenerator)

instance polynomialFiniteType : Algebra.FiniteType ℂ polynomialAlgebra :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

lemma polynomialAlgebra_map :
    polynomialAlgebra.map (IsScalarTower.toAlgHom ℂ L[X] (RatFunc L)) = algebra := by
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  apply congrArg (Algebra.adjoin ℂ)
  apply congrArg Set.range
  funext i
  simp only [Function.comp_apply, polynomialGenerator, IsScalarTower.toAlgHom_apply,
    map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rfl

def polynomialEquiv : polynomialAlgebra ≃ₐ[ℂ] algebra :=
  (polynomialAlgebra.equivMapOfInjective
    (IsScalarTower.toAlgHom ℂ L[X] (RatFunc L)) (IsFractionRing.injective L[X] (RatFunc L))).trans
    (Subalgebra.equivOfEq _ _ polynomialAlgebra_map)

lemma polynomialEquiv_coe (p : polynomialAlgebra) :
    (polynomialEquiv p : RatFunc L) = algebraMap L[X] (RatFunc L) p.val := rfl

instance polynomialFractionRing : IsFractionRing polynomialAlgebra (RatFunc L) := by
  refine IsFractionRing.of_ringEquiv_left polynomialEquiv.toRingEquiv ?_
  intro p
  change algebraMap L[X] (RatFunc L) p.val = (polynomialEquiv p : RatFunc L)
  exact (polynomialEquiv_coe p).symm

end ExplicitCone

namespace ExplicitCone
open Polynomial

abbrev pieces := GradedNormalization.piece polynomialAlgebra
abbrev completedRing := SectionCompletion.series pieces

lemma integral_polynomial_mem_cartierChart (p : L[X])
    (hp : IsIntegral polynomialAlgebra p) :
    algebraMap L[X] (RatFunc L) p ∈ cartierChart := by
  apply normalizedCone_le_cartierChart
  change IsIntegral algebra (algebraMap L[X] (RatFunc L) p)
  exact hp.map_of_comp_eq polynomialEquiv.toRingHom (algebraMap L[X] (RatFunc L))
    (by ext p; rfl)

/-- Every degree of the WHOLE normalization has regular coefficients on
the original H-chart, not merely the eighteen generating sections. -/
theorem normalized_coefficient_mem_sectionChart (n : ℕ) (a : L) (ha : a ∈ pieces n) :
    a / sectionCoefficient (0,0) ^ n ∈ sectionChart := by
  have h := PolynomialFieldChart.scaled_coefficient_mem sectionChart
    (sectionCoefficient (0,0)) sectionCoefficient_base_ne_zero (monomial n a)
    (integral_polynomial_mem_cartierChart _ ha) n
  simpa using h

end ExplicitCone


namespace KummerTriple
open KummerLines
variable (p : ℕ) [Fact p.Prime]

instance coordinateSmooth : Algebra.Smooth ℂ C where
  formallySmooth := inferInstanceAs (Algebra.FormallySmooth ℂ (MvPolynomial (Fin 2) ℂ))
  finitePresentation := inferInstanceAs (Algebra.FinitePresentation ℂ (MvPolynomial (Fin 2) ℂ))

instance planeSmooth : Algebra.Smooth ℂ (B p) :=
  Algebra.Smooth.of_equiv (planeEquiv p)

instance : Algebra ℂ (S p) :=
  ((algebraMap (B p) (S p)).comp (algebraMap ℂ (B p))).toAlgebra
instance : IsScalarTower ℂ (B p) (S p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := B p) (A := S p) rfl
instance : IsScalarTower ℂ (S p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := S p) (A := L p) (by
    rw [IsScalarTower.algebraMap_eq ℂ (B p) (L p),
      IsScalarTower.algebraMap_eq (B p) (S p) (L p)]
    rfl)

instance localizationSmooth : Algebra.Smooth ℂ (S p) :=
  Algebra.Smooth.comp ℂ (B p) (S p)

theorem chartRootAlgebra_smooth : Algebra.Smooth ℂ (chartRootAlgebra p) := by
  let := (chartRootAlgebra_finiteFreeEtale p).1
  exact Algebra.Smooth.comp ℂ (S p) (chartRootAlgebra p)

end KummerTriple
namespace ExplicitCone

theorem tripleRegularAlgebra_smooth : Algebra.Smooth ℂ tripleRegularAlgebra := by
  exact KummerTriple.chartRootAlgebra_smooth 7

end ExplicitCone


namespace KummerTripleDiagonal
open KummerLines
variable (p : ℕ) [Fact p.Prime]

instance coordinateSmooth : Algebra.Smooth ℂ C where
  formallySmooth := inferInstanceAs (Algebra.FormallySmooth ℂ (MvPolynomial (Fin 2) ℂ))
  finitePresentation := inferInstanceAs (Algebra.FinitePresentation ℂ (MvPolynomial (Fin 2) ℂ))

instance planeSmooth : Algebra.Smooth ℂ (B p) :=
  Algebra.Smooth.of_equiv (planeEquiv p)

instance : Algebra ℂ (S p) :=
  ((algebraMap (B p) (S p)).comp (algebraMap ℂ (B p))).toAlgebra
instance : IsScalarTower ℂ (B p) (S p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := B p) (A := S p) rfl
instance : IsScalarTower ℂ (S p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := S p) (A := L p) (by
    rw [IsScalarTower.algebraMap_eq ℂ (B p) (L p),
      IsScalarTower.algebraMap_eq (B p) (S p) (L p)]
    rfl)

instance localizationSmooth : Algebra.Smooth ℂ (S p) :=
  Algebra.Smooth.comp ℂ (B p) (S p)

theorem chartRootAlgebra_smooth : Algebra.Smooth ℂ (chartRootAlgebra p) := by
  let := (chartRootAlgebra_finiteFreeEtale p).1
  exact Algebra.Smooth.comp ℂ (S p) (chartRootAlgebra p)

end KummerTripleDiagonal

namespace ExplicitCone
theorem diagonalRegularAlgebra_smooth : Algebra.Smooth ℂ diagonalRegularAlgebra :=
  KummerTripleDiagonal.chartRootAlgebra_smooth 7
end ExplicitCone

namespace KummerShifted
open KummerLines
variable (p : ℕ) [Fact p.Prime]

instance coordinateSmooth : Algebra.Smooth ℂ C where
  formallySmooth := inferInstanceAs (Algebra.FormallySmooth ℂ (MvPolynomial (Fin 2) ℂ))
  finitePresentation := inferInstanceAs (Algebra.FinitePresentation ℂ (MvPolynomial (Fin 2) ℂ))

instance planeSmooth : Algebra.Smooth ℂ (B p) :=
  Algebra.Smooth.of_equiv (planeEquiv p)

instance : Algebra ℂ (S p) :=
  ((algebraMap (B p) (S p)).comp (algebraMap ℂ (B p))).toAlgebra
instance : IsScalarTower ℂ (B p) (S p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := B p) (A := S p) rfl
instance : IsScalarTower ℂ (S p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := S p) (A := L p) (by
    rw [IsScalarTower.algebraMap_eq ℂ (B p) (L p),
      IsScalarTower.algebraMap_eq (B p) (S p) (L p)]
    rfl)

instance localizationSmooth : Algebra.Smooth ℂ (S p) :=
  Algebra.Smooth.comp ℂ (B p) (S p)

theorem chartRootAlgebra_smooth : Algebra.Smooth ℂ (chartRootAlgebra p) := by
  let := (chartRootAlgebra_finiteFreeEtale p).1
  exact Algebra.Smooth.comp ℂ (S p) (chartRootAlgebra p)

end KummerShifted

namespace ExplicitCone
theorem shiftedRegularAlgebra_smooth : Algebra.Smooth ℂ shiftedRegularAlgebra :=
  KummerShifted.chartRootAlgebra_smooth 7
end ExplicitCone

namespace KummerShiftedDiagonal
open KummerLines
variable (p : ℕ) [Fact p.Prime]

instance coordinateSmooth : Algebra.Smooth ℂ C where
  formallySmooth := inferInstanceAs (Algebra.FormallySmooth ℂ (MvPolynomial (Fin 2) ℂ))
  finitePresentation := inferInstanceAs (Algebra.FinitePresentation ℂ (MvPolynomial (Fin 2) ℂ))

instance planeSmooth : Algebra.Smooth ℂ (B p) :=
  Algebra.Smooth.of_equiv (planeEquiv p)

instance : Algebra ℂ (S p) :=
  ((algebraMap (B p) (S p)).comp (algebraMap ℂ (B p))).toAlgebra
instance : IsScalarTower ℂ (B p) (S p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := B p) (A := S p) rfl
instance : IsScalarTower ℂ (S p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := S p) (A := L p) (by
    rw [IsScalarTower.algebraMap_eq ℂ (B p) (L p),
      IsScalarTower.algebraMap_eq (B p) (S p) (L p)]
    rfl)

instance localizationSmooth : Algebra.Smooth ℂ (S p) :=
  Algebra.Smooth.comp ℂ (B p) (S p)

theorem chartRootAlgebra_smooth : Algebra.Smooth ℂ (chartRootAlgebra p) := by
  let := (chartRootAlgebra_finiteFreeEtale p).1
  exact Algebra.Smooth.comp ℂ (S p) (chartRootAlgebra p)

end KummerShiftedDiagonal

namespace ExplicitCone
theorem shiftedDiagonalRegularAlgebra_smooth : Algebra.Smooth ℂ shiftedDiagonalRegularAlgebra :=
  KummerShiftedDiagonal.chartRootAlgebra_smooth 7
end ExplicitCone

namespace KummerAffineExtra
open KummerLines
variable (p : ℕ) [Fact p.Prime] (j : Fin 2)

instance coordinateSmooth : Algebra.Smooth ℂ R where
  formallySmooth := inferInstanceAs (Algebra.FormallySmooth ℂ (MvPolynomial (Fin 2) ℂ))
  finitePresentation := inferInstanceAs (Algebra.FinitePresentation ℂ (MvPolynomial (Fin 2) ℂ))

instance planeSmooth : Algebra.Smooth ℂ (B p j) :=
  Algebra.Smooth.of_equiv (planeEquiv p j)

instance : Algebra ℂ (S p j) :=
  ((algebraMap (B p j) (S p j)).comp (algebraMap ℂ (B p j))).toAlgebra
instance : IsScalarTower ℂ (B p j) (S p j) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := B p j) (A := S p j) rfl
instance : IsScalarTower ℂ (S p j) (L p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := S p j) (A := L p) (by
    rw [IsScalarTower.algebraMap_eq ℂ (B p j) (L p),
      IsScalarTower.algebraMap_eq (B p j) (S p j) (L p)]
    rfl)

instance localizationSmooth : Algebra.Smooth ℂ (S p j) :=
  Algebra.Smooth.comp ℂ (B p j) (S p j)

theorem chartRootAlgebra_smooth : Algebra.Smooth ℂ (chartRootAlgebra p j) := by
  let := (chartRootAlgebra_finiteFreeEtale p j).1
  exact Algebra.Smooth.comp ℂ (S p j) (chartRootAlgebra p j)

end KummerAffineExtra

namespace ExplicitCone
theorem affineRegularAlgebra_smooth (j : Fin 2) : Algebra.Smooth ℂ (affineRegularAlgebra j) :=
  KummerAffineExtra.chartRootAlgebra_smooth 7 j
end ExplicitCone

namespace FieldPrincipalOpen
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
variable (A : Subalgebra k L) [IsFractionRing A L] (d : A) (hd : d ≠ 0)

instance scalarTower : IsScalarTower k A (away A d hd) :=
  IsScalarTower.of_algebraMap_eq' (by ext x; rfl)

lemma away_smooth [Algebra.Smooth k A] : Algebra.Smooth k (away A d hd) := by
  let : Algebra.Smooth A (away A d hd) := Algebra.Smooth.of_isLocalization_Away d
  exact Algebra.Smooth.comp k A (away A d hd)

lemma smooth_away_of_eq (B : Subalgebra k L) [Algebra.Smooth k B]
    (h : away A d hd = B) : Algebra.Smooth k (Localization.Away d) := by
  have : Algebra.Smooth k (away A d hd) :=
    Algebra.Smooth.of_equiv (Subalgebra.equivOfEq _ _ h.symm)
  exact Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers d) (away A d hd) (Localization.Away d)).restrictScalars k)
end FieldPrincipalOpen

namespace ExplicitCone

lemma sectionChart_tripleOpen_smooth :
    Algebra.Smooth ℂ (Localization.Away tripleSectionDenominator) := by
  have := tripleRegularAlgebra_smooth
  exact FieldPrincipalOpen.smooth_away_of_eq sectionChart tripleSectionDenominator
    tripleSectionDenominator_ne_zero tripleRegularAlgebra tripleSectionOpen_eq

lemma sectionChart_diagonalOpen_smooth :
    Algebra.Smooth ℂ (Localization.Away diagonalSectionDenominator) := by
  have := diagonalRegularAlgebra_smooth
  exact FieldPrincipalOpen.smooth_away_of_eq sectionChart diagonalSectionDenominator
    diagonalSectionDenominator_ne_zero diagonalRegularAlgebra diagonalSectionOpen_eq

lemma sectionChart_shiftedOpen_smooth :
    Algebra.Smooth ℂ (Localization.Away shiftedSectionDenominator) := by
  have := shiftedRegularAlgebra_smooth
  exact FieldPrincipalOpen.smooth_away_of_eq sectionChart shiftedSectionDenominator
    shiftedSectionDenominator_ne_zero shiftedRegularAlgebra shiftedSectionOpen_eq

lemma sectionChart_shiftedDiagonalOpen_smooth :
    Algebra.Smooth ℂ (Localization.Away shiftedDiagonalSectionDenominator) := by
  have := shiftedDiagonalRegularAlgebra_smooth
  exact FieldPrincipalOpen.smooth_away_of_eq sectionChart shiftedDiagonalSectionDenominator
    shiftedDiagonalSectionDenominator_ne_zero shiftedDiagonalRegularAlgebra shiftedDiagonalSectionOpen_eq

lemma affinePunctured_smooth (j : Fin 2) : Algebra.Smooth ℂ (affinePuncturedRegular j) := by
  have := affineRegularAlgebra_smooth j
  exact FieldPrincipalOpen.away_smooth (affineRegularAlgebra j) (affineFirstRoot j) (affineFirstRoot_ne_zero j)
lemma sectionChart_affineOpen_smooth (j : Fin 2) :
    Algebra.Smooth ℂ (Localization.Away (affineSectionDenominator j)) := by
  have := affinePunctured_smooth j
  exact FieldPrincipalOpen.smooth_away_of_eq sectionChart (affineSectionDenominator j)
    (affineSectionDenominator_ne_zero j) (affinePuncturedRegular j) (affineSectionOpen_eq j)

theorem sectionChart_smooth : Algebra.Smooth ℂ sectionChart := by
  have : Algebra.FinitePresentation ℂ sectionChart :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨?_, inferInstance⟩
  apply Algebra.smoothLocus_eq_univ_iff.mp
  apply Set.eq_univ_iff_forall.mpr
  intro P
  rcases sectionChart_open_cover P.asIdeal with ht | hd | hs | hsd | ha
  · exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr sectionChart_tripleOpen_smooth) ht
  · exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr sectionChart_diagonalOpen_smooth) hd
  · exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr sectionChart_shiftedOpen_smooth) hs
  · exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr sectionChart_shiftedDiagonalOpen_smooth) hsd
  · exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr (sectionChart_affineOpen_smooth 0)) ha

end ExplicitCone


namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

/-- The uncompleted graded section algebra in a rational trivialization. -/
def polynomials : Subalgebra k (Polynomial K) where
  carrier := {f | ∀ n, f.coeff n ∈ T n}
  zero_mem' := by intro n; simp
  add_mem' := by intro f g hf hg n; simpa using (T n).add_mem (hf n) (hg n)
  one_mem' := by
    intro n
    by_cases hn : n = 0
    · subst n; simpa using SetLike.one_mem_graded T
    · simp [Polynomial.coeff_one, hn]
  mul_mem' := by
    intro f g hf hg n
    rw [Polynomial.coeff_mul]
    apply Submodule.sum_mem
    intro p hp
    have hpn := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    simpa [hpn] using SetLike.mul_mem_graded (hf p.1) (hg p.2)
  algebraMap_mem' := by
    intro a n
    rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
    split_ifs with hn
    · subst n
      simpa [Algebra.smul_def] using (T 0).smul_mem a (SetLike.one_mem_graded T)
    · exact (T n).zero_mem

lemma monomial_mem_polynomials (n : ℕ) (a : K) :
    Polynomial.monomial n a ∈ polynomials T ↔ a ∈ T n := by
  constructor
  · intro h
    simpa using h n
  · intro h m
    rw [Polynomial.coeff_monomial]
    split_ifs with hm
    · simpa [hm] using h
    · exact (T m).zero_mem


end SectionCompletion

/-! The graded structure and projective scheme of the coefficient section algebra. -/
namespace SectionCompletion
open Polynomial
open scoped DirectSum
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

/-- Degree-n polynomials inside the coefficient section algebra. -/
def homogeneous (n : ℕ) : Submodule k (polynomials T) where
  carrier := {p | ∀ m, m ≠ n → (p : K[X]).coeff m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq m hm
    change (p.val + q.val).coeff m = 0
    simp [hp m hm, hq m hm]
  smul_mem' := by
    intro a p hp m hm
    change (a • p.val).coeff m = 0
    simp [hp m hm]

lemma homogeneous_eq_monomial {n : ℕ} {p : polynomials T}
    (hp : p ∈ homogeneous T n) :
    p.val = monomial n (p.val.coeff n) := by
  ext m
  by_cases h : m = n
  · subst m; simp
  · simp only [coeff_monomial, ite_eq_right (Ne.symm h)]
    exact hp m h

instance homogeneousGradedMonoid : SetLike.GradedMonoid (homogeneous T) where
  one_mem := by intro m hm; simp [coeff_one, hm]
  mul_mem := by
    intro i j p q hp hq m hm
    change (p.val * q.val).coeff m = 0
    rw [homogeneous_eq_monomial T hp, homogeneous_eq_monomial T hq,
      monomial_mul_monomial, coeff_monomial, ite_eq_right (Ne.symm hm)]

def homogeneousPart (p : polynomials T) (n : ℕ) : homogeneous T n :=
  ⟨⟨monomial n (p.val.coeff n), (monomial_mem_polynomials T n _).mpr (p.property n)⟩,
    by intro m hm; simp [coeff_monomial, Ne.symm hm]⟩

lemma homogeneousPart_coe (p : polynomials T) (n : ℕ) :
    ((homogeneousPart T p n).val : K[X]) = monomial n (p.val.coeff n) := rfl

/-- Finite support is the actual polynomial support, not an assumption of a
formal infinite homogeneous decomposition. -/
noncomputable def decomposePolynomial (p : polynomials T) :
    ⨁ n, homogeneous T n :=
  DFinsupp.mk p.val.support (fun n => homogeneousPart T p n.val)

lemma decomposePolynomial_apply (p : polynomials T) (n : ℕ) :
    decomposePolynomial T p n = homogeneousPart T p n := by
  classical
  unfold decomposePolynomial
  rw [DFinsupp.mk_apply]
  split_ifs with h
  · rfl
  · apply Subtype.ext
    apply Subtype.ext
    change 0 = monomial n (p.val.coeff n)
    rw [notMem_support_iff.mp h, map_zero]

lemma coeff_recompose (x : ⨁ n, homogeneous T n) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (homogeneous T) x).val).coeff n =
      ((x n).val.val).coeff n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i p =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : n = i
    · subst n; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ h]
      exact p.property n h
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, coeff_add]
    exact congrArg₂ (· + ·) hx hy

noncomputable instance polynomialGradedRing : GradedAlgebra (homogeneous T) where
  decompose' := decomposePolynomial T
  left_inv := by
    intro p
    apply Subtype.ext
    ext n
    rw [coeff_recompose, decomposePolynomial_apply]
    simp [homogeneousPart_coe]
  right_inv := by
    intro x
    apply DFinsupp.ext
    intro n
    rw [decomposePolynomial_apply]
    apply Subtype.ext
    apply Subtype.ext
    change monomial n _ = _
    rw [coeff_recompose]
    exact (homogeneous_eq_monomial T (x n).property).symm

/-- The projective scheme of the actual section-coefficient algebra. -/
noncomputable def proj : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (homogeneous T)

end SectionCompletion

namespace SectionCompletion
open Polynomial AlgebraicGeometry
open scoped DirectSum
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

instance degreeZeroNontrivial : Nontrivial (homogeneous T 0) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have H := congrArg (fun a : homogeneous T 0 => a.val.val) h
  exact zero_ne_one H

instance degreeZeroTower : IsScalarTower k (homogeneous T 0) (polynomials T) where
  smul_assoc a b c := by
    change (a • b.val) * c = a • (b.val * c)
    exact smul_mul_assoc a b.val c

instance finiteType_over_degreeZero [Algebra.FiniteType k (polynomials T)] :
    Algebra.FiniteType (homogeneous T 0) (polynomials T) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k (homogeneous T 0) (polynomials T)

/-- The actual Proj structure morphism is proper. -/
instance projProper [Algebra.FiniteType k (polynomials T)] :
    IsProper (Proj.toSpecZero (homogeneous T)) := inferInstance

/-- When the degree-zero coefficient piece consists of scalars, the Proj
base is canonically the original scalar field. -/
noncomputable def zeroEquiv
    (h0 : ∀ a ∈ T 0, ∃ c : k, algebraMap k K c = a) :
    k ≃ₐ[k] homogeneous T 0 :=
  AlgEquiv.ofBijective (Algebra.ofId k (homogeneous T 0)) ⟨
    (algebraMap k (homogeneous T 0)).injective, by
    intro a
    obtain ⟨c, hc⟩ := h0 (a.val.val.coeff 0) (a.val.property 0)
    refine ⟨c, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change Polynomial.C (algebraMap k K c) = a.val.val
    rw [homogeneous_eq_monomial T a.property, ← hc, monomial_zero_left]⟩

end SectionCompletion

end


noncomputable section
namespace SectionCompletion
open Polynomial
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma adjoin_mem_ringHom_range {B : Type*} [CommRing B] (f : B →+* K)
    (hs : ∀ a : k, algebraMap k K a ∈ f.range) {ι : Type*} (v : ι → K)
    (hv : ∀ i, v i ∈ f.range) (a : K) (ha : a ∈ Algebra.adjoin k (Set.range v)) :
    a ∈ f.range := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨i,rfl⟩ := ha; exact hv i
  | algebraMap a => exact hs a
  | add a b ha hb h₁ h₂ => exact f.range.add_mem h₁ h₂
  | mul a b ha hb h₁ h₂ => exact f.range.mul_mem h₁ h₂

/-- The homogeneous degree-one section with coefficient `c`. -/
def linearSection (c : K) (hc : c ∈ T 1) : polynomials T :=
  ⟨monomial 1 c, (monomial_mem_polynomials T 1 c).mpr hc⟩

lemma linearSection_homogeneous (c : K) (hc : c ∈ T 1) :
    linearSection T c hc ∈ homogeneous T 1 := by
  intro n hn
  simp [linearSection, coeff_monomial, Ne.symm hn]

abbrev homogeneousChart (c : K) (hc : c ∈ T 1) :=
  HomogeneousLocalization.Away (homogeneous T) (linearSection T c hc)

/-- Evaluation at one, used only on degree-zero homogeneous fractions. -/
def evaluateOne : polynomials T →+* K :=
  (evalRingHom (1 : K)).comp (polynomials T).val.toRingHom

lemma evaluateOne_linearSection (c : K) (hc : c ∈ T 1) :
    evaluateOne T (linearSection T c hc) = c := by
  simp [evaluateOne, linearSection]

variable (c : K) (hc : c ∈ T 1) (hn : c ≠ 0)

def homogeneousChartMap : homogeneousChart T c hc →+* K :=
  (Localization.awayLift (evaluateOne T) (linearSection T c hc)
    (isUnit_iff_exists_inv.mpr ⟨c⁻¹, by rw [evaluateOne_linearSection]; exact mul_inv_cancel₀ hn⟩)).comp
    (algebraMap (homogeneousChart T c hc) (Localization.Away (linearSection T c hc)))

lemma homogeneousChartMap_mk (n : ℕ) (a : polynomials T)
    (ha : a ∈ homogeneous T (n • 1)) :
    homogeneousChartMap T c hc hn
      (HomogeneousLocalization.Away.mk (homogeneous T)
        (linearSection_homogeneous T c hc) n a ha) = a.val.coeff n / c ^ n := by
  simp only [homogeneousChartMap, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ _ (by rw [evaluateOne_linearSection]; exact mul_inv_cancel₀ hn)]
  have he := homogeneous_eq_monomial T (by simpa using ha : a ∈ homogeneous T n)
  change a.val.eval 1 * (c⁻¹) ^ n = _
  conv_lhs => rw [he]
  simp only [eval_monomial, one_pow, mul_one, inv_pow, div_eq_mul_inv]

lemma homogeneousChartMap_injective :
    Function.Injective (homogeneousChartMap T c hc hn) := by
  have hk : ∀ x, homogeneousChartMap T c hc hn x = 0 → x = 0 := by
    intro x hx
    obtain ⟨n,a,ha,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (homogeneous T) (linearSection_homogeneous T c hc) x
    rw [homogeneousChartMap_mk] at hx
    have hz : a.val.coeff n = 0 := (div_eq_zero_iff).mp hx |>.resolve_right (pow_ne_zero n hn)
    have az : a = 0 := by
      apply Subtype.ext
      rw [homogeneous_eq_monomial T (by simpa using ha : a ∈ homogeneous T n), hz, map_zero]
      rfl
    subst a
    apply HomogeneousLocalization.val_injective _
    simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero]
    exact Localization.mk_zero _
  intro x y h
  apply sub_eq_zero.mp
  apply hk
  rw [map_sub, h, sub_self]

lemma scaledCoefficient_mem_range (n : ℕ) (a : K) (ha : a ∈ T n) :
    a / c ^ n ∈ RingHom.range (R := homogeneousChart T c hc) (homogeneousChartMap T c hc hn) := by
  let p : polynomials T := ⟨monomial n a, (monomial_mem_polynomials T n a).mpr ha⟩
  have hp : p ∈ homogeneous T (n • 1) := by
    intro m hm
    simp only [smul_eq_mul, mul_one] at hm
    simp [p, coeff_monomial, Ne.symm hm]
  refine ⟨HomogeneousLocalization.Away.mk (homogeneous T)
    (linearSection_homogeneous T c hc) n p hp, ?_⟩
  rw [homogeneousChartMap_mk]
  simp [p]

lemma homogeneousChartMap_mem (A : Subalgebra k K)
    (hA : ∀ n a, a ∈ T n → a / c ^ n ∈ A) (x : homogeneousChart T c hc) :
    homogeneousChartMap T c hc hn x ∈ A := by
  obtain ⟨n,a,ha,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneous T) (linearSection_homogeneous T c hc) x
  rw [homogeneousChartMap_mk]
  exact hA n _ (a.property n)

/-- A literal basic affine Proj chart, identified by all normalized coefficients. -/
def homogeneousChartEquiv (A : Subalgebra k K)
    (hA : ∀ n a, a ∈ T n → a / c ^ n ∈ A)
    (hgen : ∀ a ∈ A, a ∈ RingHom.range (R := homogeneousChart T c hc) (homogeneousChartMap T c hc hn)) :
    homogeneousChart T c hc ≃+* A :=
  RingEquiv.ofBijective ((homogeneousChartMap T c hc hn).codRestrict A.toSubring
    (homogeneousChartMap_mem T c hc hn A hA)) ⟨
      fun _ _ h => homogeneousChartMap_injective T c hc hn (congrArg Subtype.val h), by
      intro a
      obtain ⟨x,hx⟩ := hgen a.val a.property
      exact ⟨x, Subtype.ext hx⟩⟩

instance homogeneousChartScalarAlgebra : Algebra k (homogeneousChart T c hc) :=
  ((algebraMap (homogeneous T 0) (homogeneousChart T c hc)).comp
    (algebraMap k (homogeneous T 0))).toAlgebra

lemma homogeneousChartMap_scalar (a : k) :
    homogeneousChartMap T c hc hn ((@algebraMap k (homogeneousChart T c hc) _ _ (homogeneousChartScalarAlgebra T c hc)) a) =
      algebraMap k K a := by
  have ha : algebraMap k (polynomials T) a ∈ homogeneous T (0 • 1) := by
    intro m hm
    change (C (algebraMap k K a)).coeff m = 0
    simp only [smul_eq_mul, zero_mul] at hm
    simp [coeff_C, hm]
  have hs : (@algebraMap k (homogeneousChart T c hc) _ _ (homogeneousChartScalarAlgebra T c hc)) a =
    HomogeneousLocalization.Away.mk (homogeneous T)
      (linearSection_homogeneous T c hc) 0 (algebraMap k (polynomials T) a) ha := by
    apply HomogeneousLocalization.val_injective _
    rfl
  rw [hs, homogeneousChartMap_mk]
  change (C (algebraMap k K a)).coeff 0 / c ^ 0 = _
  simp

def homogeneousChartAlgEquiv (A : Subalgebra k K)
    (hA : ∀ n a, a ∈ T n → a / c ^ n ∈ A)
    (hgen : ∀ a ∈ A, a ∈ RingHom.range (R := homogeneousChart T c hc)
      (homogeneousChartMap T c hc hn)) :
    homogeneousChart T c hc ≃ₐ[k] A :=
  { homogeneousChartEquiv T c hc hn A hA hgen with
    commutes' := fun a => Subtype.ext (homogeneousChartMap_scalar T c hc hn a) }

lemma adjoin_le_homogeneousChartMap_range {ι : Type*} (v : ι → K)
    (hv : ∀ i, v i ∈ T 1) (a : K)
    (ha : a ∈ Algebra.adjoin k (Set.range fun i => v i / c)) :
    a ∈ RingHom.range (R := homogeneousChart T c hc) (homogeneousChartMap T c hc hn) := by
  apply adjoin_mem_ringHom_range (homogeneousChartMap T c hc hn) (fun a => ?_)
    (fun i => v i / c) (fun i => ?_) a ha
  · exact ⟨(@algebraMap k (homogeneousChart T c hc) _ _
      (homogeneousChartScalarAlgebra T c hc)) a, homogeneousChartMap_scalar T c hc hn a⟩
  · simpa only [pow_one] using scaledCoefficient_mem_range T c hc hn 1 (v i) (hv i)

def homogeneousChartAlgEquivOfAdjoin {ι : Type*} (v : ι → K)
    (hv : ∀ i, v i ∈ T 1)
    (hA : ∀ n a, a ∈ T n → a / c ^ n ∈ Algebra.adjoin k (Set.range fun i => v i / c)) :
    homogeneousChart T c hc ≃ₐ[k] Algebra.adjoin k (Set.range fun i => v i / c) :=
  homogeneousChartAlgEquiv T c hc hn _ hA
    (adjoin_le_homogeneousChartMap_range T c hc hn v hv)

end SectionCompletion


namespace SmallCM

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

lemma dimension_le_of_integral [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
  intro P Q hPQ
  exact Ideal.IsIntegral.under_lt_under hPQ

lemma dimension_ge_of_integral [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    ringKrullDim A ≤ ringKrullDim B := by
  apply iSup_le
  intro l
  let P := Classical.choice (Ideal.nonempty_primesOver (S := B) l.head.asIdeal)
  let : P.val.IsPrime := P.property.1
  let : P.val.LiesOver l.head.asIdeal := P.property.2
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.val
  rw [← hlen]
  exact Order.LTSeries.length_le_krullDim L

lemma dimension_eq_of_integral [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    ringKrullDim B = ringKrullDim A :=
  le_antisymm (dimension_le_of_integral A B) (dimension_ge_of_integral A B)

end SmallCM

namespace SmallCM
open Algebra
lemma dimension_of_trdeg (k B : Type) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (n : ℕ) (hn : trdeg k B = n) :
    ringKrullDim B = n := by
  obtain ⟨m, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let P := MvPolynomial (Fin m) k
  let : Algebra P B := f.toRingHom.toAlgebra
  let : Module.Finite P B := hfin
  let : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective P B).mpr hf
  let : IsScalarTower k P B := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  have hm : (m : Cardinal) = n := by
    have hh := trdeg_add_eq k P (A := B)
    simpa only [P, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fin,
      Cardinal.lift_natCast, trdeg_eq_zero, add_zero, hn] using hh
  have hmn : m = n := by exact_mod_cast hm
  rw [dimension_eq_of_integral P B, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin, WithBot.coe_natCast, hmn]

lemma trdeg_fractionRing (k B F : Type) [Field k] [CommRing B] [IsDomain B]
    [Field F] [Algebra k B] [Algebra B F] [Algebra k F] [IsScalarTower k B F]
    [IsFractionRing B F] : trdeg k F = trdeg k B := by
  let : Algebra.IsAlgebraic B F := IsLocalization.isAlgebraic F (nonZeroDivisors B)
  have hh := trdeg_add_eq k B (A := F)
  simpa only [trdeg_eq_zero, add_zero] using hh.symm

end SmallCM

end

end OAI
