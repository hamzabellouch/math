import OAI.Analysis.KadisonSimilarity.FreeProduct.LocalFreeCornerInputs
import OAI.Analysis.KadisonSimilarity.Representation.CanonicalGeneratedOperators
import OAI.Analysis.KadisonSimilarity.FreeProduct.SmallFreeCornerTransport

namespace OAI

/-! The canonical free-corner estimate for a positive tracial algebra.
The estimate is expressed through the generated algebra and its
compressed tracial representation. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)
  (hφ : Function.Injective φ) (hψ : Function.Injective ψ)

local notation "L" => canonicalGeneratedAlgebra τ htr φ ψ
local notation "G" => canonicalGeneratedGeometry τ htr φ ψ
local notation "A₀" => StarAlgHom.range (canonicalGeneratedFirst τ htr φ ψ)
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τ htr φ ψ)

include hφ in
omit [PartialOrder R] [StarOrderedRing R] in
theorem canonicalFirstRange_closed : IsClosed (A₀ : Set L) :=
  codRestrict_range_isClosed L φ (canonicalGenerated_first_mem τ htr φ ψ)
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
include hψ in
omit [PartialOrder R] [StarOrderedRing R] in
theorem canonicalSecondRange_closed : IsClosed (D₀ : Set L) :=
  codRestrict_range_isClosed L ψ (canonicalGenerated_second_mem τ htr φ ψ)
    (NonUnitalStarAlgHom.isometry ψ hψ).isClosedEmbedding.isClosed_range

variable [IsClosed ((canonicalGeneratedFirst τ htr φ ψ).range :
    Set (canonicalGeneratedAlgebra τ htr φ ψ))]
  [IsClosed ((canonicalGeneratedSecond τ htr φ ψ).range :
    Set (canonicalGeneratedAlgebra τ htr φ ψ))]

variable (τR : R →ₚ[ℂ] ℂ) (hψτ : ∀ r, τ (ψ r) = τR r)

/-- Transport all small-frame data into the actual second range. -/
def canonicalSmallFrameCore {b : ℝ} (Q : SmallFreeCornerData τR.toLinearMap b) :
    SmallFreeCornerData ((G).baseGeometry D₀).trace b :=
  Q.transport (canonicalGeneratedSecond τ htr φ ψ).rangeRestrict
    τR.toLinearMap ((G).baseGeometry D₀).trace hψτ

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))
  (h1 : τ 1 = 1) (hfτ : ∀ a : P, τ (star a * a) = 0 → a = 0)

local notation "M₀" => canonicalGeneratedMatrices τ htr φ ψ τR hψτ M

/-- The exact local structural input, with the native trace and faithfulness
proofs supplied by the canonical generated model. -/
abbrev CanonicalFreeCornerCoreInput {b : ℝ}
    (_Q : SmallFreeCornerData ((G).baseGeometry D₀).trace b)
    (_x : A) (_hxsq : _x * _x = 1) : Prop :=
  let _matrices := M₀
  let _faithful := canonicalGenerated_faithful τ htr φ ψ hfτ
  (G).LocalFreeCornerPublishedInputs

include h1 in
/-- Apply the local theorem after the actual compression to the canonical
algebra. The statement estimates the same compression used in recovery. -/
theorem canonical_free_corner_bound
    (hf : ScalarFree τ.toLinearMap φ.range ψ.range)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {b : ℝ} (Q : SmallFreeCornerData ((G).baseGeometry D₀).trace b)
    (x : A) (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τ (φ x) = 0)
    (published : CanonicalFreeCornerCoreInput τ htr φ ψ τR hψτ M hfτ Q x hxsq)
    (baseExpectation : Nonempty (TracialExpectation (G).trace A₀))
    (hnormal : ∃ N : VonNeumannAlgebra (canonicalGeneratedTrace τ htr φ ψ).GNS,
      (G).left.range = N.toStarSubalgebra)
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hcomm : ∀ r, T.comp (τ.gnsStarAlgHom (ψ r)) =
      (τ.gnsStarAlgHom (ψ r)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : (gnsTracialGeometry τ htr).TraceCornerBound ψ.range T Q.trace ε) :
    ‖(G).baseOperator A₀
      (commutator (canonicalGeneratedOperator τ htr φ ψ T)
        ((G).left (canonicalGeneratedFirst τ htr φ ψ x)))‖ ≤ cornerConstant * ε := by
  let s : A₀ := ⟨canonicalGeneratedFirst τ htr φ ψ x, ⟨x, rfl⟩⟩
  have hsstar : star s = s := by
    apply Subtype.ext
    change star (canonicalGeneratedFirst τ htr φ ψ x) =
      canonicalGeneratedFirst τ htr φ ψ x
    rw [← map_star, hxstar]
  have hssq : s * s = 1 := by
    apply Subtype.ext
    change (canonicalGeneratedFirst τ htr φ ψ x) *
      (canonicalGeneratedFirst τ htr φ ψ x) = 1
    rw [← map_mul, hxsq, map_one]
  have hs0 : (G).trace (s : L) = 0 := hx0
  exact (G).free_corner_from_local_published_inputs A₀ D₀ M₀ Q s hssq h1
    (canonicalGenerated_faithful τ htr φ ψ hfτ) published baseExpectation hnormal
    (canonicalGenerated_generation τ htr φ ψ)
    (canonicalGeneratedRealSequence τ htr φ ψ τR hψτ S) hsize
    (canonicalGenerated_freeness τ htr φ ψ hf).symm hsstar hs0
    (canonicalGeneratedOperator τ htr φ ψ T)
    (canonicalGeneratedOperator_commutes τ htr φ ψ T hcomm) hε
    (canonicalGeneratedOperator_traceCornerBound τ htr φ ψ T hcorner)

end KadisonSimilarity

end

end OAI
