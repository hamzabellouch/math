import OAI.Probability.SLE.Loewner.SlitSupport
import Mathlib.Topology.CompactOpen

namespace OAI

/-! The clock-free open-tube specialization of the published support input.

Tran–Yuan (2020), *A support theorem for SLE curves*, Corollary 1.2
(strong topology, i.e. modulo increasing reparameterization). Its
simple-curve inclusion, with the usual capacity normalization/dilation,
gives the specialization below for a geometric simple path. Only positivity
for each fixed tube is assumed; no uniformity over tubes or pasts is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

local instance geometricTubePathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance geometricTubePathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def pathTubeEvent (N V : Set ℂ) : Set C(ℝ≥0, ℂ) :=
  {f | ∃ T : ℝ≥0, 0 < T ∧ MapsTo f (Icc 0 T) N ∧ f T ∈ V}

theorem isOpen_pathTubeEvent {N V : Set ℂ} (hN : IsOpen N) (hV : IsOpen V) :
    IsOpen (pathTubeEvent N V) := by
  have he : pathTubeEvent N V = ⋃ T : ℝ≥0, ⋃ (_ : 0 < T),
      {f : C(ℝ≥0, ℂ) | MapsTo f (Icc 0 T) N} ∩
        (fun f : C(ℝ≥0, ℂ) => f T) ⁻¹' V := by
    ext f
    simp only [pathTubeEvent, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor <;> rintro ⟨T, hT, hN, hV⟩ <;> exact ⟨T, hT, hN, hV⟩
  rw [he]
  exact isOpen_iUnion (fun T => isOpen_iUnion (fun _ =>
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hN).inter
      (hV.preimage (continuous_eval_const T))))

theorem measurableSet_pathTubeEvent {N V : Set ℂ} (hN : IsOpen N) (hV : IsOpen V) :
    MeasurableSet (pathTubeEvent N V) := (isOpen_pathTubeEvent hN hV).measurableSet

/-- A precise small consequence of the simple-curve inclusion in Tran–Yuan,
Corollary 1.2, suited to the actual geometric continuation route. -/
def PublishedGeometricTubeSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ (z : ℂ) (p : Path (0 : ℂ) z), Function.Injective p →
    (∀ t, t ≠ 0 → p t ∈ upperHalfPlane) →
    ∀ N V : Set ℂ, IsOpen N → IsOpen V → range p ⊆ N → z ∈ V →
      0 < P {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) N ∧ γ ω T ∈ V}

/-- The geometrically stated published input applies directly to the Borel
passage event on continuous-path space. -/
theorem geometric_tube_passage_of_published_support
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → C(ℝ≥0, ℂ))
    (hpublished : PublishedGeometricTubeSupport P (fun ω => f ω))
    (z : ℂ) (p : Path (0 : ℂ) z) (hp : Function.Injective p)
    (hpH : ∀ t, t ≠ 0 → p t ∈ upperHalfPlane)
    (N V : Set ℂ) (hN : IsOpen N) (hV : IsOpen V)
    (hpN : range p ⊆ N) (hzV : z ∈ V) :
    0 < P (f ⁻¹' pathTubeEvent N V) :=
  hpublished z p hp hpH N V hN hV hpN hzV

end SLEExactGauge

end

end OAI
