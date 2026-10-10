import OAI.Analysis.KadisonSimilarity.FreeProduct.UltrapowerFreePositionTransfer
import OAI.Analysis.KadisonSimilarity.Tracial.GeneratedGNSRecovery

namespace OAI

/-! The two compressions used in the finite-factor argument are combined
here. The resulting operator on the generated algebra retains commutation,
all prescribed small-corner bounds, and the original commutator norm. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "Pω" => Ultrapower τB hB ω trB
local notation "τQ" => quotientTrace τB hB ω trB
local notation "Φ" => tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ

variable (L D : StarSubalgebra ℂ (Ultrapower τB hB ω trB))
  [IsClosed (L : Set (Ultrapower τB hB ω trB))]

local instance generatedAlgebraCStar : CStarAlgebra L := inferInstance
local instance generatedAlgebraOrder : PartialOrder L := inferInstance
local instance generatedAlgebraStarOrder : StarOrderedRing L := inferInstance
local instance generatedPreGNSNorm :
    SeminormedAddCommGroup (restrictedPositiveTrace (quotientTrace τB hB ω trB) L).PreGNS :=
  inferInstance
local instance generatedGNSNorm :
    NormedAddCommGroup (restrictedPositiveTrace (quotientTrace τB hB ω trB) L).GNS :=
  inferInstance
local instance generatedGNSInner :
    InnerProductSpace ℂ (restrictedPositiveTrace (quotientTrace τB hB ω trB) L).GNS :=
  inferInstance

/-- The concrete operator after Hilbert-ultrapower and generated-algebra
compression. No operator on the generated algebra is chosen independently. -/
def generatedUltrapowerOperator (T : τB.GNS →L[ℂ] τB.GNS) :
    (restrictedPositiveTrace τQ L).GNS →L[ℂ] (restrictedPositiveTrace τQ L).GNS :=
  generatedGNSCompression τQ L (tracialUltrapowerCompression τB hB ω trB T)

theorem generatedUltrapowerOperator_commutes
    (hD : D ≤ (Φ).range) (T : τB.GNS →L[ℂ] τB.GNS)
    (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
      (τB.gnsStarAlgHom (φ a)).comp T) :
    ∀ a : D.comap L.subtype,
      (generatedUltrapowerOperator τB hB ω trB L T).comp
          ((restrictedPositiveTrace τQ L).gnsStarAlgHom (a : L)) =
        ((restrictedPositiveTrace τQ L).gnsStarAlgHom (a : L)).comp
          (generatedUltrapowerOperator τB hB ω trB L T) :=
  generatedGNSCompression_commutes τQ L D _
    (tracialUltrapowerCompression_commutes_subalgebra τA τB hA hB ω trA trB
      φ hφ D hD T hcomm)

theorem generatedUltrapowerOperator_traceCornerBound
    (rounding : SpectralProjectionRoundingInput τA) (hD : D ≤ (Φ).range)
    (T : τB.GNS →L[ℂ] τB.GNS) {ε s t : ℝ} (hε : 0 ≤ ε) (hts : t < s)
    (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ s →
      ∀ z : CStarCorner (φ q) (hq.map φ),
        ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖) :
    (gnsTracialGeometry (restrictedPositiveTrace τQ L)
      (restrictedPositiveTrace_tracial τQ L (quotientTrace_tracial τB hB ω trB))).TraceCornerBound
        (D.comap L.subtype) (generatedUltrapowerOperator τB hB ω trB L T) t ε :=
  generatedGNSCompression_traceCornerBound τQ L (quotientTrace_tracial τB hB ω trB)
    D _ (included_ultrapower_traceCornerBound τA τB hA hB ω trA trB φ hφ
      rounding D hD T hε hts hcorner)

/-- A bound from the free-corner theorem on this generated algebra controls
the original operator on its original GNS space, with the identical constant. -/
theorem norm_commutator_le_generatedUltrapowerOperator
    (hconst : ∀ b, constant τB hB ω trB b ∈ L)
    (T : τB.GNS →L[ℂ] τB.GNS) (b : B) :
    ‖commutator T (τB.gnsStarAlgHom b)‖ ≤
      ‖(gnsTracialGeometry (restrictedPositiveTrace τQ L)
          (restrictedPositiveTrace_tracial τQ L (quotientTrace_tracial τB hB ω trB))).baseOperator
        ((constant τB hB ω trB).codRestrict L hconst).range
        (commutator (generatedUltrapowerOperator τB hB ω trB L T)
          ((restrictedPositiveTrace τQ L).gnsStarAlgHom
            ((constant τB hB ω trB).codRestrict L hconst b)))‖ :=
  norm_commutator_le_generated_GNS_compression τB τQ L (constant τB hB ω trB)
    hconst (quotientTrace_constant τB hB ω trB) (quotientTrace_tracial τB hB ω trB)
    T (tracialUltrapowerCompression τB hB ω trB T)
    (constant_compression_tracialUltrapower τB hB ω trB T) b

end KadisonSimilarity

end

end OAI
