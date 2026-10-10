import OAI.Probability.SLE.Mass.DiskLevelTests

namespace OAI

/-! The centered physical-disk estimate survives the canonical convex
limit on the same event and with its original target-radius factor. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem uniform_disk_terminal_test_centered_moments
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : IsCompact K) (hKd : K ⊆ ball 0 1)
    (b : ℝ) (hb : 0<b) (hb1 : b≤1) (hbK : ∀ x∈K, b≤1-‖x‖^2) (m : ℕ) :
    ∃ M : ℝ≥0∞, M<∞ ∧ ∀ (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi),
      ∀ f : C_c((ball (0:ℂ) 1),ℝ), (∀ x, 0≤f x) → (∀ x, f x≤1) →
        (∀ x : (ball (0:ℂ) 1), (x:ℂ)∉K → f x=0) → ∀ e : ℝ, 0<e → e≤1 →
      (∫⁻ ω in diskCenterHit γ G θ e,
        ENNReal.ofReal (∫ x, f x ∂conformalMass (Target.diskHomeomorph θ hθ)
          (Target.diskMassWeight κ θ hθ) (C.rational.terminal ω)) ^ m ∂P) ≤
            M*ENNReal.ofReal (e^codimension κ) := by
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨M,hM,hbound⟩ := uniform_diskLevelMass_centered_moments hB hm hBm hc h0 hκ hκ8
    γ G F hw hgrowth K hK hKd b hb hb1 hbK m
  refine ⟨M,hM,?_⟩
  intro θ hθ f hf hf1 hfs e he he1
  let g := conformalMassTest (Target.diskHomeomorph θ hθ) (Target.diskMassWeight κ θ hθ) f
  have hg : ∀ z, 0≤g z := fun z => mul_nonneg (NNReal.coe_nonneg _) (hf _)
  simp_rw [conformalMass_integral]
  apply level_radon_limit_test_moment_le hm hc hκ hκ8 γ G F hw
    (fun n => (n:ℝ)) (fun n => Nat.cast_nonneg n)
    C.rational.supports C.rational.weights C.rational.weights_nonneg C.rational.weights_sum
    ∞ C.rational.terminal (ae_restrict_of_ae C.rational.terminal_limit) g hg m
    (M*ENNReal.ofReal (e^codimension κ))
  intro n
  apply (lintegral_mono (fun ω => pow_le_pow_left' ?_ m)).trans (hbound θ hθ e he he1 n (Nat.cast_nonneg n))
  simpa only [g,conformalMass_integral] using
    ofReal_disk_level_test_le hm hc hκ hκ8 γ G F hw θ hθ K hK hKd f hf hf1 hfs
      n (Nat.cast_nonneg n) ∞ ω

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
