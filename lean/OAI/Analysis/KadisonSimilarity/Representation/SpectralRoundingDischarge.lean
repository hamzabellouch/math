import OAI.Analysis.KadisonSimilarity.Representation.SpectralStepDischarge
import OAI.Analysis.KadisonSimilarity.Tracial.TracialProjectionLifting

namespace OAI

/-! # The one-half spectral rounding inequality

The cutoff is the support of the positive part of `2a-1`.  Its polynomial
order inequality implies the required L² inequality for every positive
functional on a concrete von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual half-threshold spectral projection. -/
def halfSpectralProjection (a : H →L[ℂ] H) : H →L[ℂ] H :=
  rangeSupport (2 * a - 1)⁺

theorem halfSpectralProjection_isStarProjection (a : H →L[ℂ] H) :
    IsStarProjection (halfSpectralProjection a) := rangeSupport_isStarProjection _

theorem halfSpectralProjection_mem (P : VonNeumannAlgebra H)
    (a : H →L[ℂ] H) (ha : a ∈ P) : halfSpectralProjection a ∈ P :=
  positive_rangeSupport_mem P _ (P.toStarSubalgebra.sub_mem
    (by simpa only [two_mul] using P.toStarSubalgebra.add_mem ha ha) P.one_mem)

theorem halfSpectralProjection_commutes (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    Commute (halfSpectralProjection a) a := by
  have h : Commute (2 * a - 1) a := by
    change (2 * a - 1) * a = a * (2 * a - 1)
    noncomm_ring
  have hp : Commute (2 * a - 1)⁺ a := by
    rw [CFC.posPart_def]
    exact h.cfcₙ_real _
  exact rangeSupport_commutes _ a hp (by simpa only [ha.star_eq] using hp)

/-- Pure operator order form of the scalar cutoff estimate. -/
theorem halfSpectralProjection_square_le (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    (halfSpectralProjection a - a) ^ 2 ≤ 4 * (a * a - a) ^ 2 := by
  let p := halfSpectralProjection a
  let q := 1 - p
  let x := 2 * a - 1
  have hp : IsStarProjection p := halfSpectralProjection_isStarProjection a
  have hpa : Commute p a := halfSpectralProjection_commutes a ha
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hppt (b : H →L[ℂ] H) : p * (p * b) = p * b := by rw [← mul_assoc, hpp]
  have hxt : IsSelfAdjoint x := by
    change star (2 * a - 1) = 2 * a - 1
    simp only [star_sub, star_mul, star_ofNat, star_one, ha.star_eq]
    noncomm_ring
  have hxpos : 0 ≤ x * p := by
    have he := shifted_mul_upperSpectralCut x hxt 0
    have he' : x * p = x⁺ := by simpa only [zero_smul, sub_zero, upperSpectralCut, p,
      halfSpectralProjection, x] using he
    rw [he']
    exact CFC.posPart_nonneg x
  have hxneg : 0 ≤ (-x) * q := by
    have he := shifted_mul_complement_upperSpectralCut x hxt 0
    have he' : x * q = -x⁻ := by simpa only [zero_smul, sub_zero, upperSpectralCut, p, q,
      halfSpectralProjection, x] using he
    simpa only [neg_mul, he', neg_neg] using CFC.negPart_nonneg x
  have hfirst : 0 ≤ 4 * a ^ 2 * p - p := by
    have hid : 4 * a ^ 2 * p - p = (x * p) ^ 2 + 2 • (x * p) := by
      dsimp [x]
      noncomm_ring [hpa.eq, hpa.left_comm, hpp, hppt]
    rw [hid]
    exact add_nonneg hxpos.isSelfAdjoint.sq_nonneg (nsmul_nonneg hxpos 2)
  have hsecond : 0 ≤ 4 * (a - 1) ^ 2 * q - q := by
    have hid : 4 * (a - 1) ^ 2 * q - q = ((-x) * q) ^ 2 + 2 • ((-x) * q) := by
      dsimp [x, q]
      noncomm_ring [hpa.eq, hpa.left_comm, hpp, hppt]
    rw [hid]
    exact add_nonneg hxneg.isSelfAdjoint.sq_nonneg (nsmul_nonneg hxneg 2)
  have h1 := star_left_conjugate_nonneg hfirst (a - 1)
  have h2 := star_left_conjugate_nonneg hsecond a
  have heq : star (a - 1) * (4 * a ^ 2 * p - p) * (a - 1) +
      star a * (4 * (a - 1) ^ 2 * q - q) * a =
      4 * (a * a - a) ^ 2 - (p - a) ^ 2 := by
    simp only [star_sub, ha.star_eq, star_one]
    dsimp [q]
    noncomm_ring [hpa.eq, hpa.left_comm, hpp, hppt]
  apply sub_nonneg.mp
  rw [← heq]
  exact add_nonneg h1 h2

private instance vonNeumann_closed (P : VonNeumannAlgebra H) :
    IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _

/-- Passing the polynomial order estimate through a positive functional. -/
theorem preGNS_rounding_norm_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (a p : A)
    (ha : IsSelfAdjoint a) (hp : IsSelfAdjoint p)
    (horder : (p - a) ^ 2 ≤ 4 * (a * a - a) ^ 2) :
    ‖τ.toPreGNS (p - a)‖ ≤ 2 * ‖τ.toPreGNS (a * a - a)‖ := by
  have hτ := τ.monotone horder
  have hpa : IsSelfAdjoint (p - a) := hp.sub ha
  have hdef : IsSelfAdjoint (a * a - a) := by
    simpa only [sq] using (ha.pow 2).sub ha
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  have hleft : ‖τ.toPreGNS (p - a)‖ ^ 2 = (τ ((p - a) ^ 2)).re := by
    simp only [norm_sq_eq_re_inner (𝕜 := ℂ), PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, hpa.star_eq, sq]
    rfl
  have hright : ‖τ.toPreGNS (a * a - a)‖ ^ 2 = (τ ((a * a - a) ^ 2)).re := by
    simp only [norm_sq_eq_re_inner (𝕜 := ℂ), PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, hdef.star_eq, sq]
    rfl
  rw [hleft, hright]
  have hmap : τ (4 * (a * a - a) ^ 2) = 4 * τ ((a * a - a) ^ 2) := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using map_nsmul τ 4 ((a * a - a) ^ 2)
  change τ ((p - a) ^ 2) ≤ τ (4 * (a * a - a) ^ 2) at hτ
  rw [hmap] at hτ
  convert hτ.1 using 1
  norm_num

theorem isStarProjection_subtype_of_coe {R S : Type*} [Mul R] [Star R]
    [SetLike S R] [MulMemClass S R] [StarMemClass S R] {s : S}
    (x : s) (hp : IsStarProjection (x : R)) : IsStarProjection x := by
  constructor
  · exact Subtype.ext hp.isIdempotentElem.eq
  · exact Subtype.ext hp.isSelfAdjoint.star_eq

theorem isStarProjection_subtype_mk {R : Type*} [Semiring R] [StarRing R]
    [Algebra ℂ R] [StarModule ℂ R] (S : StarSubalgebra ℂ R) (x : R) (hx : x ∈ S)
    (hp : IsStarProjection x) : IsStarProjection (⟨x, hx⟩ : S) :=
  isStarProjection_subtype_of_coe _ hp

section VonNeumann
variable (P : VonNeumannAlgebra H)

/-- The spectral projection as an element of the von Neumann algebra. -/
def halfSpectralProjectionElement (a : P.toStarSubalgebra) : P.toStarSubalgebra :=
  ⟨halfSpectralProjection a, halfSpectralProjection_mem P a a.property⟩

theorem halfSpectralProjectionElement_isStarProjection (a : P.toStarSubalgebra) :
    IsStarProjection (halfSpectralProjectionElement P a) := by
  have he : (halfSpectralProjectionElement P a : H →L[ℂ] H) =
      halfSpectralProjection (a : H →L[ℂ] H) := rfl
  apply isStarProjection_subtype_of_coe
  rw [he]
  exact halfSpectralProjection_isStarProjection (H := H) (a : H →L[ℂ] H)

theorem halfSpectralProjectionElement_square_le (a : P.toStarSubalgebra)
    (ha : IsSelfAdjoint a) :
    (halfSpectralProjectionElement P a - a) ^ 2 ≤ 4 * (a * a - a) ^ 2 := by
  change (halfSpectralProjection (a : H →L[ℂ] H) - a) ^ 2 ≤ 4 * (a * a - a) ^ 2
  exact halfSpectralProjection_square_le (H := H) (a : H →L[ℂ] H)
    (show IsSelfAdjoint (a : H →L[ℂ] H) from congrArg Subtype.val ha.star_eq)

local instance roundingCStar : CStarAlgebra P.toStarSubalgebra := {}
local instance roundingOrder : PartialOrder P.toStarSubalgebra := inferInstance
local instance roundingStarOrder : StarOrderedRing P.toStarSubalgebra :=
  Subtype.starOrderedRing P.toStarSubalgebra
local instance roundingCFC :
    NonUnitalContinuousFunctionalCalculus ℝ P.toStarSubalgebra IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
local instance roundingDecompose : SelfAdjointDecompose P.toStarSubalgebra where
  exists_nonneg_sub_nonneg {a} ha :=
    ⟨a⁺, a⁻, CFC.posPart_nonneg a, CFC.negPart_nonneg a, (CFC.posPart_sub_negPart a ha).symm⟩

variable (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ)
local instance roundingPreGNSNorm : SeminormedAddCommGroup τ.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := τ.preGNSpreInnerProdSpace)

theorem halfSpectralProjectionElement_norm_le (a : P.toStarSubalgebra)
    (ha : IsSelfAdjoint a) :
    ‖τ.toPreGNS (halfSpectralProjectionElement P a - a)‖ ≤
      2 * ‖τ.toPreGNS (a * a - a)‖ :=
  preGNS_rounding_norm_le τ a (halfSpectralProjectionElement P a) ha
    (halfSpectralProjectionElement_isStarProjection P a).isSelfAdjoint
    (halfSpectralProjectionElement_square_le P a ha)

/-- The tracial-ultrapower rounding input follows from the concrete spectral
projection. In fact positivity of the functional is enough for this step. -/
theorem spectralProjectionRoundingInput :
    @SpectralProjectionRoundingInput P.toStarSubalgebra (roundingCStar P)
      (roundingOrder P) (roundingStarOrder P) τ :=
  fun a ha => ⟨halfSpectralProjectionElement P a,
    halfSpectralProjectionElement_isStarProjection P a,
    halfSpectralProjectionElement_norm_le P τ a ha⟩

end VonNeumann

end KadisonSimilarity

end

end OAI
