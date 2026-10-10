import OAI.Probability.SLE.Loewner.RawDiskAngleTail
import OAI.Probability.SLE.Gauge.CanonicalDiskMomentTails

namespace OAI

/-! Arbitrary finite radius levels are bounded by the same countable tail
supremum already used in the prescribed-gauge budget. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass
local instance arbitraryTailMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance arbitraryTailBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma limitingDiskTail_le_one
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (b : ℝ) : C.limitingDiskTail hc b ≤ 1 := by
  apply iSup_le
  intro j
  let := centeredDiskLaw_isProbability hB hBm hc hκ hκ8 γ G F hw
    (4*(j:ℝ)/κ) (by positivity)
  exact (measure_mono (subset_univ _)).trans_eq measure_univ

lemma centeredDiskTail_le_limit
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (b v : ℝ) (hv : 0≤v) : C.centeredDiskTail hc b v ≤ C.limitingDiskTail hc b := by
  obtain ⟨n,hn⟩ := exists_nat_ge (v*κ/4)
  have hnV : v≤4*(n:ℝ)/κ := (le_div_iff₀ hκ).mpr (by linarith)
  exact (C.centeredDiskTail_mono hB hc h0 hκ hκ8 F hw b hv
    (show 0≤4*(n:ℝ)/κ from by positivity) hnV).trans (le_iSup (fun j : ℕ => C.centeredDiskTail hc b (4*(j:ℝ)/κ)) n)

lemma raw_angle_tail_average_le_limit
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (b v : ℝ) (hv : 0≤v) :
    (∫⁻ θ, R.angleDiskTail (P.map (sourceDriverPath B hc)) κ b v θ ∂Target.angleLaw κ) ≤
      C.limitingDiskTail hc b := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  rw [R.angleDiskTail_average _ κ hκ b v,C.raw_centeredDiskTail_eq hc hκ F hw R he v b hv]
  exact C.centeredDiskTail_le_limit hB hc h0 hκ hκ8 F hw b v hv

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
