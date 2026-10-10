import OAI.Probability.SLE.Angle.CanonicalAngleMixing
import OAI.Probability.SLE.Gauge.PrescribedOrdinaryTransfer

namespace OAI

/-! The first paper's prescribed moment gauge, from precisely named
published inputs. The angular mixing estimate is proved internally. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance prescribedPublishedMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance prescribedPublishedBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

/-- The exact prescribed gauge gives positive finite mass to every positive-time
compact trace segment and finite expected mass of the whole trace in bounded disks.
Published inputs: Duren (1983), section 2.3 (the disk univalent-growth estimate),
and Rohde--Schramm (2005), Theorem 5.1 (trace generation under the driver law). -/
theorem RegularSLEPresentation.prescribed_main_of_published_inputs
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0<κ) (hκ8 : κ<8) (hγ : ∀ t, Measurable (fun ω => γ ω t))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (htrace : PublishedTraceGeneration
      ((P.comap (Subtype.val : a.samples → Ω)).map (sourceDriverPath a.B a.continuous_B))
      κ (fun t p => p t))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    MainConclusion P (Target.gauge κ W) γ := by
  have : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  have hBm : Measurable (Function.uncurry a.B) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  apply a.prescribed_main_of_canonical_angle_bounds hκ hκ8 hγ hgrowth htrace W hW
    (angleSpectralMixingTime κ) (angleSpectralMixingTime_pos hκ)
  exact canonicalAngleAverage_uniform_bounds a.brownian hBm a.continuous_B a.zero_B
    hκ hκ8 (fun ω => γ ω) a.G a.F a.witness

/-- The first paper's full prescribed-gauge Hausdorff conclusion for ordinary
chordal SLE, with only the cited published conformal and trace inputs. -/
theorem ordinary_prescribed_mainConclusion_of_published_inputs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (htrace : PublishedTraceGeneration (ordinaryRegularDriverLaw hSLE) κ (fun t p => p t))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    MainConclusion P (Target.gauge κ W) γ :=
  (ordinaryRegularPresentation hSLE).prescribed_main_of_published_inputs
    hκ hκ8 hSLE.1 hgrowth htrace W hW

end SLEExactGauge

end

end OAI
