import OAI.Probability.SLE.Gauge.PrescribedCanonicalMixing
import OAI.Probability.SLE.Gauge.CanonicalPrescribedUpper

namespace OAI

/-! A uniform canonical angle transition bound implies the prescribed-gauge
upper cover estimate. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance upperAngleMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance upperAngleBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem CanonicalMass.prescribed_expectation_of_canonical_angle_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0 < κ) (hκ8 : κ < 8)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (D : Set C(ℝ≥0,ℝ)) (hD : MeasurableSet D)
    (hDf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈D)
    (hDp : ∀ p∈D, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (hγ : ∀ t, Measurable (fun ω => γ ω t))
    (δ : ℝ) (hδ : 0<δ)
    (hangle : ∀ (v : ℝ), δ≤v → ∀ (f : ℝ → ℝ≥0∞), Measurable f →
      ∀ θ∈Ioo (0:ℝ) Real.pi, (∫⁻ φ, f φ ∂Target.angleLaw κ)/2 ≤
        canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ)
    (L : ℝ) (hL : 0≤L) (K : Set ℂ) (hK : IsClosed K)
    (hKL : K⊆closedBall 0 L) (hH : ∀ z∈K, 0≤z.im) :
    (∫⁻ ω, Target.hausdorff (Target.gauge κ W) (range (γ ω)∩K) ∂P)<∞ := by
  classical
  have hm1 := C.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW 1
  have hJn (n : ℕ) := C.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n
  have hdata (n : ℕ) : ∃ (J : ℕ) (e : Fin J → ℤ×ℕ),
      (∀ i, (e i).2<Target.multiplicity κ W n (e i).1) ∧
      (3≤n → Function.Injective e ∧
        (∀ kj, kj∈range e ↔ kj.2<Target.multiplicity κ W n kj.1) ∧
        StrictMono (fun i => Target.entryPosition κ W (n,some (e i)))) := by
    by_cases hn : 3≤n
    · obtain ⟨J,e,hi,he,ho⟩ := Target.ordered_repeated_batch κ W (by omega) hm1 (hJn n)
      exact ⟨J,e,fun i => (he _).mp ⟨i,rfl⟩,fun _ => ⟨hi,he,ho⟩⟩
    · refine ⟨0,Fin.elim0,?_,?_⟩
      · exact fun i => Fin.elim0 i
      · exact fun h => False.elim (hn h)
  choose J e hentries horder using hdata
  apply C.prescribed_expectation_of_finite_failures hB hc h0 hκ hκ8 F hw hγ hpublished
    hgrowth W hW J e hentries (4096*Real.pi) ((128*Real.pi)^dimension κ) L
    (by have hp := Real.pi_gt_three; linarith) (Real.rpow_pos_of_pos (by positivity) _) hL K hK hKL hH
  filter_upwards [Target.eventually_prescribedTestPastLevel_gap hκ W
      (by positivity : 0<2048*Real.pi) δ,
    Target.eventually_entryPhysicalLevel_large hκ W (by positivity : 0<2048*Real.pi) 0,
    eventually_ge_atTop 3] with n hgap hlevel hn
  intro ij _hij hy
  let z := prescribedGridCenter (Target.entryRadius κ W (n,none)) ij
  have hz : z∈upperHalfPlane := lt_of_lt_of_le (Real.exp_pos _) hy
  obtain ⟨hi,he',ho⟩ := horder n hn
  exact C.prescribed_batch_failure_of_canonical_angle_bound hB hc h0 hκ hκ8 F hw R he
    D hD hDf hDp hgrowth hpublished W hW hn (e n) hi he' ho z hz
    (fun o => (hlevel o z hy).le) δ hδ (hgap (J n) (e n) ho z hy) hangle

end SLEExactGauge.Multipoint

end

end OAI
