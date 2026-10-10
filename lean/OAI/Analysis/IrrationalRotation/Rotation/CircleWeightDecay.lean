import OAI.Analysis.IrrationalRotation.Rotation.RotationDecay
import OAI.Analysis.IrrationalRotation.Rotation.UniformRotationAverage
import OAI.Analysis.IrrationalRotation.Analysis.TruncatedLogIntegral
import OAI.Analysis.IrrationalRotation.Analysis.ExponentialDecay
import OAI.Analysis.IrrationalRotation.Rotation.AnalyticWeightBridge

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace InvariantProjection.CircleWeightDecay

local instance circleWeightDecayPeriodPos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev Circle := AddCircle (1 : ℝ)

theorem all_rates_decay {θ : ℝ} (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂AddCircle.haarAddCircle, 0 < f x)
    (hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂AddCircle.haarAddCircle) = ∞) :
    ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, ∀ x : Circle,
      (∏ k ∈ range n, f (x + k • (θ : Circle))) ≤ Real.exp (-a * n) := by
  have h := RotationDecay.all_rates_orbitProduct_decay
    (σ := fun y : Circle => y + (θ : Circle)) hf0 ?_
  · simpa only [RotationDecay.orbitProduct, add_right_iterate] using h
  intro a ha
  obtain ⟨M, hM⟩ := Invariant233.exists_truncated_log_integral_lt f f.continuous.measurable
    hf0 hf1 hpos hlog (2 * a)
  let l : C(Circle, ℝ) := ⟨RotationDecay.truncatedLog f M,
    Invariant233.continuous_truncated_log f f.continuous M⟩
  refine ⟨M, ∫ x, l x ∂AddCircle.haarAddCircle, ?_, ?_⟩
  · change (∫ x, Real.log (max (f x) (Real.exp (-(M : ℝ))))
      ∂AddCircle.haarAddCircle) < -2 * a
    simpa only [neg_mul] using hM
  · exact UniformRotationAverage.tendstoUniformly_real hθ l

def orbitProductC (θ : ℝ) (f : C(Circle, ℝ)) (n : ℕ) : C(Circle, ℝ) :=
  ∏ k ∈ range n, f.comp ⟨fun x => x + k • (θ : Circle),
    continuous_id.add continuous_const⟩

@[simp] lemma orbitProductC_apply (θ : ℝ) (f : C(Circle, ℝ)) (n : ℕ) (x : Circle) :
    orbitProductC θ f n x = ∏ k ∈ range n, f (x + k • (θ : Circle)) := by
  simp [orbitProductC]

lemma orbitProductC_nonneg (θ : ℝ) (f : C(Circle, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) (x : Circle) :
    0 ≤ orbitProductC θ f n x := by
  rw [orbitProductC_apply]
  exact prod_nonneg fun k _ => hf0 _

theorem all_rates_norm_decay {θ : ℝ} (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂AddCircle.haarAddCircle, 0 < f x)
    (hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂AddCircle.haarAddCircle) = ∞) :
    ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop,
      ‖orbitProductC θ f n‖ ≤ Real.exp (-a * n) := by
  intro a ha
  filter_upwards [all_rates_decay hθ f hf0 hf1 hpos hlog a ha] with n hn
  apply (ContinuousMap.norm_le _ (Real.exp_nonneg _)).mpr
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (orbitProductC_nonneg θ f hf0 n x),
    orbitProductC_apply]
  exact hn x

theorem tendsto_norm_root_zero {θ : ℝ} (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂AddCircle.haarAddCircle, 0 < f x)
    (hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂AddCircle.haarAddCircle) = ∞) :
    Tendsto (fun n : ℕ => ‖orbitProductC θ f n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) :=
  Invariant233.tendsto_root_zero_of_exponential_decay
    (fun n => ‖orbitProductC θ f n‖) (fun _ => norm_nonneg _)
    (all_rates_norm_decay hθ f hf0 hf1 hpos hlog)

lemma circleMeasure_eq_haar : Invariant233.circleMeasure =
    (AddCircle.haarAddCircle : Measure Circle) := by
  change (volume : Measure Circle) = _
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num

theorem all_rates_decay_of_isContinuousCircleWeight {θ : ℝ} (hθ : Irrational θ)
    {f : Invariant233.Circle → ℝ} (hf : Invariant233.IsContinuousCircleWeight f) :
    ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, ∀ x : Circle,
      (∏ k ∈ range n, f (x + k • (θ : Circle))) ≤ Real.exp (-a * n) := by
  have hpos : ∀ᵐ x ∂AddCircle.haarAddCircle, 0 < f x := by
    rw [← circleMeasure_eq_haar]
    exact hf.ae_pos
  have hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂AddCircle.haarAddCircle) = ∞ := by
    rw [← circleMeasure_eq_haar]
    exact (Invariant233.hasNegInfiniteLogIntegral_iff_of_ae_pos f hf.ae_pos).mp hf.2.2.2
  exact all_rates_decay hθ ⟨f, hf.1⟩ (fun x => (hf.2.1 x).1)
    (fun x => (hf.2.1 x).2) hpos hlog

end InvariantProjection.CircleWeightDecay

end

end OAI
