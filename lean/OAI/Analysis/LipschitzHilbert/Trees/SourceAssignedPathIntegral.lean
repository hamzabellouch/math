import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedLabelCount
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedVertexPath
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedSelectorPlaneIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathAmplitudeCongr

namespace OAI

/-! Exact adapters for applying the supported plane theorem to the
inhabited assigned reference families. The original packet values,
coefficient integrals and path predictions are preserved. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- No geometric condition is lost when empty label fibers are removed. -/
theorem inhabitedFamily_topGeometry (P : SourceLabeledLattice N κ Label Item)
    (T : SlopeBox) (K : ℝ) (D : ℕ) (h : SourceLabeledTopGeometry P T K D) :
    SourceLabeledTopGeometry P.inhabitedFamily T K D := by
  refine ⟨h.length_le,h.width_le,?_,?_,h.order_le,h.scale_eq⟩
  · intro j l u
    exact h.centerX_le j (P.inhabitedOriginalLabel j l) u
  · intro j l u
    exact h.centerZ_le j (P.inhabitedOriginalLabel j l) u

/-- Original coefficient masks and all three raw jets are unchanged. -/
theorem inhabitedFamily_maskedRawBand (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (mask : ℝ) (jet : Fin 3)
    (j : Fin N) (x y : ℝ) :
    (P.inhabitedFamily.withProfile (P.inhabitedAlternate alt)
      (P.inhabitedAlternate_bound alt hAlt)).rawBand
      (fun j l u => mask • P.inhabitedFamily.physicalMultiplierCoefficient t
        (fun j l => b j (P.inhabitedOriginalLabel j l)) v f j l u) jet j x y =
    (P.withProfile alt hAlt).rawBand
      (fun j l u => mask • P.physicalMultiplierCoefficient t b v f j l u) jet j x y := by
  exact (P.withProfile alt hAlt).inhabitedFamily_rawBand
    (fun j l u => mask • P.physicalMultiplierCoefficient t b v f j l u) jet j x y

theorem inhabitedFamily_rawInterval_original (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (jet : Fin 3)
    (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    (P.inhabitedFamily.withProfile (P.inhabitedAlternate alt)
      (P.inhabitedAlternate_bound alt hAlt)).rawInterval
      (P.inhabitedFamily.physicalMultiplierCoefficient t
        (fun j l => b j (P.inhabitedOriginalLabel j l)) v f) jet lower upper x y =
    (P.withProfile alt hAlt).rawInterval
      (P.physicalMultiplierCoefficient t b v f) jet lower upper x y := by
  exact (P.withProfile alt hAlt).inhabitedFamily_rawInterval
    (P.physicalMultiplierCoefficient t b v f) jet lower upper hlu x y

variable (P : SourceLabeledLattice N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "halt" => assignedReferenceAlternate_bound P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "selector" => assignedReferenceSelector P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

def assignedInhabitedReference (top : τ) := (Q top).inhabitedFamily

theorem assignedInhabitedReference_constant (top : τ) :
    (P.assignedInhabitedReference packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency top).constant = (F*cone+2)*P.absoluteConstant := by
  unfold assignedInhabitedReference assignedReferenceFamily constant absoluteConstant
    inhabitedFamily referenceFamily assignedTopFamily
  ring

theorem assignedInhabitedReference_short
    (hshort : ∀ q ∈ packets, P.length q.1 ≤ (T (assigned q)).length)
    (top : τ) (j : Fin N) (l : (Q top).inhabitedLabels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (Q top).inhabitedFamily.length j ≤ (T top).length :=
  P.assignedTopReference_supported_length packets assigned top oldSlope (R top)
    cone w F hw hcone hF hwide hfrequency T hshort j
    ((Q top).inhabitedOriginalLabel j l) u

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

/-- This is the value supplied to the supported plane theorem. -/
def assignedInhabitedBand (L A : ℝ) (z : ℝ×ℝ) (p : τ×Fin N) : EuclideanSpace ℂ κ :=
  ((Q p.1).inhabitedFamily.withProfile ((Q p.1).inhabitedAlternate (alts alt p.1))
    ((Q p.1).inhabitedAlternate_bound (alts alt p.1) (halt alt hAlt p.1))).rawBand
    (fun j l u => (T p.1).mask L A z •
      (Q p.1).inhabitedFamily.physicalMultiplierCoefficient (T p.1).slope
        (fun j l => selector b p.1 j ((Q p.1).inhabitedOriginalLabel j l)) v f j l u)
    0 p.2 z.1 (z.2-(T p.1).slope*z.1)

theorem assignedInhabitedBand_original (L A : ℝ) (z : ℝ×ℝ) (p : τ×Fin N)
    (hcondition : ∀ q ∈ packets,
      P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1) :
    P.assignedInhabitedBand packets assigned T oldSlope R cone w F hw hcone hF hwide hfrequency
      alt hAlt b v f L A z p =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned (Sigma.mk j (Sigma.mk l u)))) L A packets assigned z p := by
  unfold assignedInhabitedBand
  rw [(Q p.1).inhabitedFamily_maskedRawBand]
  exact P.assignedReference_rawBand_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z p.1 p.2
    (fun q hq hqt => by simpa only [hqt] using hcondition q hq)


variable (L A : ℝ) (grid : AngularGrid) (tops : Finset τ)
  (precision : τ → ℝ) (cut : ℝ) (weight : τ → (ℝ×ℝ) → ℝ)
  (K : ℕ) (gap : ℕ → ℝ)
  (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
  (hcondition : ∀ q ∈ packets,
    P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1)
  (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a : ℝ)

local notation "original" => physicalMaskedValue P alt hAlt oldSlope b v f
  (fun j l u => T (assigned (Sigma.mk j (Sigma.mk l u)))) L A
local notation "bands" => assignedInhabitedBand P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt b v f L A

include hassigned hcondition in
theorem assignedInhabitedAmplitude_original (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) :
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      packets assigned (fun q => stop (assigned q) q.1) (original z) phase a z level cell =
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (bands z) phase a z level cell := by
  rw [P.physicalMaskedAmplitude_top_bands alt hAlt oldSlope b v f
    (fun j l u => T (assigned (Sigma.mk j (Sigma.mk l u)))) L A grid tops (fun t => (T t).slope)
    precision cut weight K gap packets assigned hassigned stop phase a z level cell]
  apply congrArg (fun values : τ×Fin N → EuclideanSpace ℂ κ =>
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      values phase a z level cell)
  funext p
  exact (P.assignedInhabitedBand_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z p hcondition).symm

include hassigned hcondition in
/-- The actual active-path integrand is precisely the one integrated by
 the supported inhabited-family plane theorem. -/
theorem assignedInhabitedActivePath_original {Kb : ℕ}
    (α p M : ℝ) (shift : Fin Kb) (top : τ) (count : ℕ) (z : ℝ×ℝ) :
    grid.sourceActivePathValue tops (fun t => (T t).slope) precision cut weight K gap
      packets assigned (fun q => stop (assigned q) q.1) original
      phase a α p M shift top count z =
    grid.sourceActivePathValue tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2) bands
      phase a α p M shift top count z := by
  apply grid.sourceActivePathValue_congr_amplitude tops (fun t => (T t).slope) precision cut weight K gap
    packets assigned (fun q => stop (assigned q) q.1) original
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2) bands
    phase a z _ α p M shift top count
  exact P.assignedInhabitedAmplitude_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A grid tops precision cut weight K gap
    hassigned hcondition stop phase a z

include hassigned hcondition in
theorem assignedInhabitedPrediction_original {Kb : ℕ}
    (p μ : ℝ) (shift : Fin Kb) (top : τ) (j : ℕ) (z : ℝ×ℝ) :
    grid.sourceShiftedPathPrediction tops (fun t => (T t).slope) precision cut weight K gap
      packets assigned (fun q => stop (assigned q) q.1) original
      phase a p μ shift top z j =
    grid.sourceShiftedPathPrediction tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2) bands
      phase a p μ shift top z j := by
  apply grid.sourceShiftedPathPrediction_congr_amplitude tops (fun t => (T t).slope) precision cut weight K gap
    packets assigned (fun q => stop (assigned q) q.1) original
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2) bands
    phase a z _ p μ shift top j
  exact P.assignedInhabitedAmplitude_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A grid tops precision cut weight K gap
    hassigned hcondition stop phase a z

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
