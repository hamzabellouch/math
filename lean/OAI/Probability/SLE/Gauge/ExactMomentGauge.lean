import OAI.Probability.SLE.Geometry.CanonicalDiskPositive
import OAI.Probability.SLE.Mass.MomentLevels

namespace OAI

/-! Positive finite prescribed moments and the resulting exact quadratic gauge.
All coefficients are the original nested Wiener integrals in `Target`. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)
  (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
  (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
  (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)

include C hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW

lemma finiteMoment_positive (ℓ : ℝ) (hℓ : 0≤ℓ) (hsmall : Real.exp (-(4*ℓ/κ))<1/8) :
    0<Target.finiteMoment κ W 1 ℓ := by
  let : IsProbabilityMeasure (Target.angleLaw κ) := Target.angleLaw_isProbability hκ
  rw [C.finiteMoment_eq_levelCoefficientIntegral hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ 1]
  have hp : ∀ᵐ θ ∂Target.angleLaw κ, 0<Target.levelCoefficient κ W ℓ 1 θ := by
    filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
    exact C.levelCoefficient_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW θ hθ ℓ hℓ hsmall
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono (fun _ h => h.le))
    (C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ 1).2).2
  have he : (Target.angleLaw κ) (Function.support (Target.levelCoefficient κ W ℓ 1))=
      (Target.angleLaw κ) univ := measure_congr (hp.mono (fun θ h => propext
        (show Target.levelCoefficient κ W ℓ 1 θ≠0 ↔ True from iff_true_intro h.ne')))
  rw [he,measure_univ]
  exact zero_lt_one

theorem moment_one_positive : 0<Target.moment κ W 1 := by
  let ℓ : ℝ := κ*Real.log 16/4
  have hℓ : 0≤ℓ := div_nonneg (mul_nonneg hκ.le (Real.log_nonneg (by norm_num))) (by norm_num)
  have hlevel : 4*ℓ/κ=Real.log 16 := by dsimp only [ℓ]; field_simp
  have hsmall : Real.exp (-(4*ℓ/κ))<1/8 := by
    rw [hlevel,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<16)]
    norm_num
  have hp := C.finiteMoment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW ℓ hℓ hsmall
  apply hp.trans_le
  obtain ⟨n,hn⟩ := exists_nat_ge ℓ
  apply ge_of_tendsto (C.finiteMoment_tendsto_moment hB hc h0 hκ hκ8 F hw hgrowth W hW 1)
  filter_upwards [eventually_ge_atTop n] with j hj
  exact C.finiteMoment_mono hB hc h0 hκ hκ8 F hw hgrowth W hW 1 hℓ
    (by change (0:ℝ)≤(j:ℝ); exact Nat.cast_nonneg j) (hn.trans (Nat.cast_le.mpr hj))

theorem moment_positive (n : ℕ) : 0<Target.moment κ W n :=
  (pow_pos (C.moment_one_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW) n).trans_le
    (C.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n)

theorem prescribed_gauge_admissible : Target.IsHausdorffGauge (Target.gauge κ W) :=
  Target.gauge_admissible_of_moment_inequalities hκ hκ8 W
    (C.moment_one_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW)
    (fun n _ => C.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n)

theorem prescribed_batch_retains_moment (n : ℕ) :
    1≤Target.batchLevel κ W n ∧ 3*Target.moment κ W n/4<
      Target.finiteMoment κ W n (Target.batchLevel κ W n) := by
  apply Target.batchLevel_retains_moment κ W n
  · intro i j hij
    exact C.finiteMoment_mono hB hc h0 hκ hκ8 F hw hgrowth W hW n
      (by change (0:ℝ)≤(i:ℝ); exact Nat.cast_nonneg i)
      (by change (0:ℝ)≤(j:ℝ); exact Nat.cast_nonneg j) (Nat.cast_le.mpr hij)
  · exact C.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW n
  · exact C.finiteMoment_tendsto_moment hB hc h0 hκ hκ8 F hw hgrowth W hW n

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
