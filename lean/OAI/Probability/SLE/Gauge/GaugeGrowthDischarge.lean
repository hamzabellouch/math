import OAI.Probability.SLE.Loewner.ActualDiskGrowth
import OAI.Probability.SLE.Gauge.GaugeTraceDischarge
import OAI.Probability.SLE.Multipoint.MultipointOrdinaryProbability
import OAI.Probability.SLE.Mass.CanonicalMassConstruction

namespace OAI

/-! The prescribed gauge, multipoint estimate, and canonical mass
construction for ordinary chordal SLE. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem ordinary_prescribed_mainConclusion
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    MainConclusion P (Target.gauge κ W) γ :=
  ordinary_prescribed_mainConclusion_of_univalent_growth P κ hκ hκ8 γ hSLE
    actual_diskUnivalentGrowth W hW

theorem RegularSLEPresentation.physical_multipoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (m : ℕ) (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane) (z : Fin m → ℂ)
    (hz : ∀ i, z i ∈ upperHalfPlane) (hne : Function.Injective z)
    (b e : Fin m → ℝ) (hb : ∀ i, 0 < b i) (he : ∀ i, 0 < e i)
    (hbR : ∀ i, b i ≤ 2*(z i).im*‖deriv J (z i)‖)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (J (z i)) (J (z j))) :
    (P.comap (Subtype.val : a.samples → Ω))
      {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
        physicalConformalRadius J (a.G ω) t (z i) ≤ e i} ≤
      ENNReal.ofReal (multipointConstant κ m * ∏ i, min 1 ((e i/b i)^(1-κ/8))) :=
  a.physical_multipoint_main hκ hκ8 actual_diskUnivalentGrowth m J hJ hJinj z hz hne
    b e hb he hbR hsep

theorem RegularSLEPresentation.canonical_mass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    Nonempty (Multipoint.CanonicalMass (P.comap (Subtype.val : a.samples → Ω)) κ a.B
      (measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B)
      (fun ω => γ ω) a.G) :=
  a.canonical_mass_main hκ hκ8 actual_diskUnivalentGrowth

end SLEExactGauge

end

end OAI
