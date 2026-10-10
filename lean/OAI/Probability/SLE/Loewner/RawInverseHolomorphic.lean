import OAI.Probability.SLE.Loewner.RawInverseDriverApproximation
import OAI.Probability.SLE.Loewner.LoewnerInverseCompactness
import OAI.Probability.SLE.Geometry.ActualCompactAvoidance
import OAI.Probability.SLE.Loewner.UnivalentInverseAnalytic

namespace OAI

/-! Holomorphicity of every continuous-driver raw inverse follows from
interior approximation by actual SLE witnesses. The argument uses the
finite Brownian driver tubes, not geometric SLE support. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

theorem raw_inverse_holomorphic_of_witness_approximation
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n))
    (b : Target.Driver) (T : ℝ≥0) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hUb : ∀ n t, t ∈ Icc 0 T → |U n t-b t| ≤ δ n) :
    DifferentiableOn ℂ (Target.inverseFlow 1 b T) upperHalfPlane := by
  obtain ⟨σ,f,hσ,hf,hconv⟩ := inverse_family_subsequence U γ G F hw T
  have he (w : ℂ) (hwH : w ∈ upperHalfPlane) : f w=Target.inverseFlow 1 b T w :=
    tendsto_nhds_unique (hconv.tendsto_at hwH)
      ((raw_inverse_limit_of_witness_drivers U γ G F hw b T δ hδ hUb hwH).comp hσ.tendsto_atTop)
  exact hf.congr (fun w hwH => (he w hwH).symm)

theorem RegularSLEPresentation.raw_inverse_holomorphic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (b : Target.Driver) (T : ℝ≥0) :
    DifferentiableOn ℂ (Target.inverseFlow 1 b T) upperHalfPlane := by
  let δ (n : ℕ) : ℝ := 1/((n : ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hex (n : ℕ) : ∃ ω : a.samples,
      ∀ t ∈ Icc 0 (T+1), |Real.sqrt κ*a.B t ω-b t| < δ n := by
    have hp := regular_scaled_driver_tube_positive a hκ b.toContinuousMap
      (show b.toContinuousMap 0=0 from map_zero b) (T+1) (by positivity) (hδ n)
    exact nonempty_of_measure_ne_zero hp.ne'
  choose ω hω using hex
  exact raw_inverse_holomorphic_of_witness_approximation
    (fun n t => Real.sqrt κ*a.B t (ω n)) (fun n => γ (ω n))
    (fun n => a.G (ω n)) (fun n => a.F (ω n)) (fun n => a.witness (ω n)) b T δ
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n t ht => (hω n t
      ⟨ht.1,ht.2.trans (le_add_of_nonneg_right zero_le)⟩).le)

lemma Target.inverseFlow_injOn (b : Driver) (T : ℝ≥0) :
    InjOn (inverseFlow 1 b T) upperHalfPlane := by
  intro z hz w hw he
  have hh := congrArg (fun q => flow 1 b q T) he
  rwa [flow_inverseFlow 1 (by norm_num) b T z hz,
    flow_inverseFlow 1 (by norm_num) b T w hw] at hh

theorem RegularSLEPresentation.raw_inverse_deriv_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (b : Target.Driver) (T : ℝ≥0) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    deriv (Target.inverseFlow 1 b T) z ≠ 0 :=
  univalent_deriv_ne_zero isOpen_upperHalfPlane (a.raw_inverse_holomorphic hκ b T)
    (Target.inverseFlow_injOn b T) hz

end SLEExactGauge

end

end OAI
