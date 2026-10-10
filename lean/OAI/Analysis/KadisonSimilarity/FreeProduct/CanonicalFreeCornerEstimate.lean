import OAI.Analysis.KadisonSimilarity.FreeProduct.CanonicalFreeCornerCore
import OAI.Analysis.KadisonSimilarity.Representation.CanonicalGeneratedOperators
import OAI.Analysis.KadisonSimilarity.Tracial.UltrapowerGeneratedTransfer
import OAI.Analysis.KadisonSimilarity.FreeProduct.SmallFreeCornerTransport
import OAI.Analysis.KadisonSimilarity.Tracial.UltrapowerNormality
import OAI.Analysis.KadisonSimilarity.Representation.RestrictedNormality
import OAI.Analysis.KadisonSimilarity.Representation.CanonicalBaseExpectation
import OAI.Analysis.KadisonSimilarity.FreeProduct.CanonicalFreeFactorComparison

namespace OAI

/-! The original operator is recovered after applying the local free-corner
argument in the actual generated GNS model. All generation, faithfulness,
and compression requirements are proved here; the remaining local hypotheses
are the explicitly cited published structural inputs. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open TracialCornerGeometry
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder R] [StarOrderedRing R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (τR : R →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "Pω" => Ultrapower τB hB ω trB
local notation "τQ" => quotientTrace τB hB ω trB
local notation "trQ" => quotientTrace_tracial τB hB ω trB
local notation "ι" => constant τB hB ω trB
local notation "Φ" => tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ

variable (ψ : R →⋆ₐ[ℂ] Ultrapower τB hB ω trB)
  (hψτ : ∀ r, quotientTrace τB hB ω trB (ψ r) = τR r)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  (hψ : Function.Injective ψ)

local notation "L" => canonicalGeneratedAlgebra τQ trQ ι ψ
local notation "G" => canonicalGeneratedGeometry τQ trQ ι ψ
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τQ trQ ι ψ)

/-- The chosen closed-range proof is included inside this data type. -/
def CanonicalSecondFrame (b : ℝ) : Type _ := by
  letI : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τQ trQ ι ψ hψ
  exact SmallFreeCornerData ((G).baseGeometry D₀).trace b

/-- The fixed small frame transported into the actual free second factor. -/
def canonicalGeneratedSmallFrame {b : ℝ} (Q : SmallFreeCornerData τR.toLinearMap b) :
    CanonicalSecondFrame τB hB ω trB ψ hψ b := by
  letI : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τQ trQ ι ψ hψ
  exact canonicalSmallFrameCore (τ := τQ) (htr := trQ) (φ := ι) (ψ := ψ)
    (τR := τR) (hψτ := hψτ) Q

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

/-- Published local data on the exact canonical free-product model. -/
abbrev CanonicalFreeCornerInput {b : ℝ}
    (Q : CanonicalSecondFrame τB hB ω trB ψ hψ b)
    (x : B) (hxsq : x * x = 1) : Prop := by
  letI : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τQ trQ ι ψ hψ
  letI : IsClosed (StarAlgHom.range (canonicalGeneratedFirst τQ trQ ι ψ) : Set L) :=
    canonicalFirstRange_closed τQ trQ ι ψ (constant_injective τB hB ω trB hfB)
  exact CanonicalFreeCornerCoreInput (τ := τQ) (htr := trQ) (φ := ι) (ψ := ψ)
    (τR := τR) (hψτ := hψτ) (M := M)
    (hfτ := quotientTrace_faithful τB hB ω trB) Q x hxsq

include hfB in
/-- The generated-factor comparison used by the local application is proved
from the normal source, rather than supplied independently. -/
theorem canonicalFreeCornerInput_of_normal_source
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hf : ScalarFree (quotientTrace τB hB ω trB).toLinearMap
      (constant τB hB ω trB).range ψ.range)
    (hsource : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {b : ℝ} (Q : CanonicalSecondFrame τB hB ω trB ψ hψ b)
    (x : B) (hxsq : x * x = 1) :
    CanonicalFreeCornerInput τB τR hB ω trB ψ hψτ hψ M Q x hxsq := by
  change (G).LocalFreeCornerPublishedInputs
  exact canonicalFreeFactorComparison τQ trQ ι ψ
    (constant_injective τB hB ω trB hfB) hψ τR hψτ M
    (quotientTrace_one τB hB ω trB) (quotientTrace_faithful τB hB ω trB)
    hf hsource hsize ⟨_, canonicalGenerated_normal_range τQ trQ
      (ultrapower_trace_balls_closed τB hB ω trB hω) ι ψ⟩

include hfB in
/-- A centered symmetry in the original finite algebra obeys the free-corner
bound. The tested operator is the original GNS operator, not a separately
chosen operator on a model. -/
theorem original_symmetry_bound_of_free_corner
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hD : ψ.range ≤ (Φ).range)
    (hf : ScalarFree (quotientTrace τB hB ω trB).toLinearMap
      (constant τB hB ω trB).range ψ.range)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {b : ℝ} (Q : CanonicalSecondFrame τB hB ω trB ψ hψ b)
    (x : B) (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τB x = 0)
    (source_balls : ∀ C : ℝ, IsClosed (gnsTracialVector τB '' Metric.closedBall (0 : B) C))
    (published : CanonicalFreeCornerInput τB τR hB ω trB ψ hψτ hψ M Q x hxsq)
    (rounding : SpectralProjectionRoundingInput τA)
    (T : τB.GNS →L[ℂ] τB.GNS)
    (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
      (τB.gnsStarAlgHom (φ a)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ b →
      ∀ z : CStarCorner (φ q) (hq.map φ),
        ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖) :
    ‖commutator T (τB.gnsStarAlgHom x)‖ ≤ cornerConstant * ε := by
  have : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τQ trQ ι ψ hψ
  have : IsClosed (StarAlgHom.range (canonicalGeneratedFirst τQ trQ ι ψ) : Set L) :=
    canonicalFirstRange_closed τQ trQ ι ψ (constant_injective τB hB ω trB hfB)
  have hxQ : τQ (ι x) = 0 := by rw [quotientTrace_constant, hx0]
  have hamb := included_ultrapower_traceCornerBound τA τB hA hB ω trA trB
    φ hφ rounding ψ.range hD T hε Q.trace_lt hcorner
  have hnativecomm := fun r =>
    tracialUltrapowerCompression_commutes_subalgebra τA τB hA hB ω trA trB
      φ hφ ψ.range hD T hcomm ⟨ψ r, ⟨r, rfl⟩⟩
  have hnormal := canonicalGenerated_normal_range τQ trQ
    (ultrapower_trace_balls_closed τB hB ω trB hω) ι ψ
  have hbase := canonicalFirstRange_expectation τQ trQ ι ψ τB
    (quotientTrace_constant τB hB ω trB) (constant_injective τB hB ω trB hfB)
    source_balls (quotientTrace_one τB hB ω trB)
    (quotientTrace_faithful τB hB ω trB) ⟨_, hnormal⟩
  have hlocal := canonical_free_corner_bound (τ := τQ) (htr := trQ)
    (φ := ι) (ψ := ψ)
    (τR := τR) (hψτ := hψτ) (M := M)
    (h1 := quotientTrace_one τB hB ω trB)
    (hfτ := quotientTrace_faithful τB hB ω trB)
    hf S hsize Q x hxstar hxsq hxQ published hbase ⟨_, hnormal⟩
    (tracialUltrapowerCompression τB hB ω trB T) hnativecomm hε hamb
  exact (norm_commutator_le_generatedUltrapowerOperator τB hB ω trB L
    (canonicalGenerated_first_mem τQ trQ ι ψ) T x).trans hlocal

end KadisonSimilarity

end

end OAI
