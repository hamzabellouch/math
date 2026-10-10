import OAI.Probability.SLE.Mass.CanonicalMassConstruction
import OAI.Probability.SLE.Mass.RadonTerminalUniqueness
import OAI.Probability.SLE.Geometry.RestartInitialGreenIntegral

namespace OAI

/-! Positive initial Green mass and terminal exhaustion give a positive
probability of nonzero canonical mass at a finite deterministic time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma initialGreenMeasure_univ_pos (κ : ℝ) : 0 < initialGreenMeasure κ univ := by
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal (initialGreen κ z)) := by
    unfold initialGreen
    fun_prop
  have he : initialGreenMeasure κ univ =
      ∫⁻ z in upperHalfPlane, ENNReal.ofReal (initialGreen κ z) ∂volume := by
    simpa only [lintegral_const,Measure.restrict_univ,one_mul] using
      initialGreenMeasure_lintegral κ (fun _ => 1)
  rw [he,lintegral_pos_iff_support hm,Measure.restrict_apply (measurableSet_support hm)]
  have hs : Function.support (fun z : ℂ => ENNReal.ofReal (initialGreen κ z)) ∩ upperHalfPlane =
      upperHalfPlane := by
    ext z
    constructor
    · exact fun h => h.2
    · intro hz
      exact ⟨(ENNReal.ofReal_pos.mpr (initialGreen_pos κ z hz)).ne',hz⟩
  rw [hs]
  exact isOpen_upperHalfPlane.measure_pos (μ:=volume) ⟨Complex.I,by simp [upperHalfPlane]⟩

namespace CanonicalMass

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma exists_nonzero_finite_time : ∃ n : ℕ, 0<P {ω | C.process n ω≠0} := by
  by_contra! hzero
  have hn (n : ℕ) : ∀ᵐ ω ∂P, C.process n ω=0 := by
    rw [ae_iff]
    exact le_zero_iff.mp (hzero n)
  have ht : ∀ᵐ ω ∂P, ∀ t, C.process t ω=0 := by
    filter_upwards [ae_all_iff.mpr hn,C.paths] with ω hω hp
    intro t
    obtain ⟨n,hn⟩ := exists_nat_ge (t:ℝ)
    have hle := hp.monotone (show t≤(n:ℝ≥0) by exact_mod_cast hn)
    rw [hω n] at hle
    exact le_antisymm hle bot_le
  have hterminal : C.rational.terminal =ᵐ[P] (fun _ => 0) := by
    filter_upwards [ht,C.paths,C.exhaustion] with ω hω hp he
    let := (C.rational.terminal_radon ω).1
    apply radon_terminal_eq_of_common_exhaustion (C.rational.terminal ω) 0
      (fun t => C.process t ω) hp.dominated (fun t => by rw [hω t]) he
    intro K hK
    simp only [Measure.zero_sub,Measure.coe_zero,Pi.zero_apply]
    exact tendsto_const_nhds
  have hmean : initialGreenMeasure κ=0 := by
    rw [← C.rational.mean,Measure.bind_congr_right hterminal,Measure.bind_zero_right']
  have hp := initialGreenMeasure_univ_pos κ
  simp only [hmean,Measure.coe_zero,Pi.zero_apply,lt_self_iff_false] at hp

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
