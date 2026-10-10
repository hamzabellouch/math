import OAI.Probability.SLE.Mass.PastThresholdMass

namespace OAI

/-! Specialization of the half-mass threshold comparison to canonical mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint

lemma compactWeightedMass_one (K : Set upperHalfPlane) (μ : Measure upperHalfPlane) :
    compactWeightedMass (ContinuousMap.const _ (1:ℝ≥0)) K μ=(μ K).toReal := by
  simp [compactWeightedMass,measureReal_def]

namespace CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

lemma past_threshold_detects_half_terminal
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (q : ℕ → ℝ≥0) (hq : DenseRange q) (K : Set upperHalfPlane) (hK : IsCompact K)
    (H : ℝ) (hH : 0<H) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (2*H)<C.rational.terminal ω K →
      C.rational.terminal ω K≤2*C.rational.terminal ω (K ∩ ⋃ n,
        if H<(C.process (q n) ω K).toReal then
          {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 (q n)}ᶜ else ∅) := by
  have hp : ∀ᵐ ω ∂P, ∀ n, C.process (q n) ω=(C.rational.terminal ω).restrict
      {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 (q n)} := by
    apply ae_all_iff.mpr
    intro n
    simpa only [atTime,extendedCanonicalMass,ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe]
      using C.atTime_eq_restrict_past hB hBm hc h0 hκ hκ8 F hw (q n)
  have hs := C.compactWeightedMass_paths (ContinuousMap.const _ (1:ℝ≥0)) K hK
  filter_upwards [hp,hs] with ω hpω hsω
  intro hlarge
  let μ := C.rational.terminal ω
  let := (C.rational.terminal_radon ω).2
  let f : ℝ≥0 → ℝ := fun t => compactWeightedMass (ContinuousMap.const _ (1:ℝ≥0)) K (C.process t ω)
  have hf : Continuous f := hsω.2.2.1
  have hf0 : f 0=0 := hsω.2.1
  have hflim : Tendsto f atTop (𝓝 (μ K).toReal) := by
    simpa only [f,μ,compactWeightedMass_one] using hsω.2.2.2.1
  have hfpast (n : ℕ) : μ (K ∩ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 (q n)})=
      ENNReal.ofReal (f (q n)) := by
    have hfin : C.process (q n) ω K≠∞ := by
      let := (C.radon (q n) ω).2
      exact hK.measure_lt_top.ne
    rw [show f (q n)=(C.process (q n) ω K).toReal from compactWeightedMass_one K _,
      ENNReal.ofReal_toReal hfin,hpω n,Measure.restrict_apply hK.measurableSet]
  have h := past_threshold_detects_half μ K hK.measure_lt_top.ne
    (fun t => {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t})
    (fun t => ((isCompact_Icc.image (hw ω).1).isClosed.preimage continuous_subtype_val).measurableSet)
    q hq f hf hf0 hflim hfpast H hH hlarge
  simpa only [f,compactWeightedMass_one] using h

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
