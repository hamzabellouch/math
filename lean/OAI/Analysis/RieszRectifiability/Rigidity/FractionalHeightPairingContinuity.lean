import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalWeightedDecay

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

theorem height_fractional_test_integrable_and_bound (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hmean : (∫ y, g y) = 0) :
    Integrable (fun x => f x • fractionalSchwartzTest p g x) μ ∧
      ‖∫ x, f x • fractionalSchwartzTest p g x ∂μ‖ ≤
        fractionalSchwartzWeightedSize p g * (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ) := by
  let W := fractionalSchwartzWeightedSize p g
  have hm : Measurable (fun x => f x • fractionalSchwartzTest p g x) := by
    simp_rw [RCLike.real_smul_eq_coe_mul]
    exact (Complex.continuous_ofReal.measurable.comp hf).mul (fractionalSchwartzTest_measurable p g)
  have hb (x : Ambient (p + 1)) : ‖f x • fractionalSchwartzTest p g x‖ ≤
      W * (|f x| * polynomialDecay (p + 3) x) := by
    rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
    calc
      _ ≤ |f x| * (W * polynomialDecay (p + 3) x) :=
        mul_le_mul_of_nonneg_left (fractionalSchwartzTest_polynomial_decay p g hmean x) (abs_nonneg _)
      _ = _ := by ring
  have hi : Integrable (fun x => W * (|f x| * polynomialDecay (p + 3) x)) μ := hweight.const_mul W
  have hp : Integrable (fun x => f x • fractionalSchwartzTest p g x) μ :=
    hi.mono' hm.aestronglyMeasurable (Eventually.of_forall hb)
  refine ⟨hp, ?_⟩
  calc
    _ ≤ ∫ x, ‖f x • fractionalSchwartzTest p g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, W * (|f x| * polynomialDecay (p + 3) x) ∂μ := integral_mono hp.norm hi hb
    _ = _ := integral_const_mul W _

theorem height_fractional_test_integral_tendsto (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (G : ℕ → 𝓢(Ambient (p + 1), ℂ)) (g : 𝓢(Ambient (p + 1), ℂ))
    (ht : Tendsto G atTop (𝓝 g)) (hG : ∀ j, (∫ y, G j y) = 0) (hg : (∫ y, g y) = 0) :
    Tendsto (fun j => ∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ)
      atTop (𝓝 (∫ x, f x • fractionalSchwartzTest p g x ∂μ)) := by
  let H := fun j => G j - g
  have hHt : Tendsto H atTop (𝓝 0) := by
    simpa only [sub_self] using! ht.sub (tendsto_const_nhds (x := g))
  have hHm (j : ℕ) : (∫ y, H j y) = 0 := by
    change (∫ y, G j y - g y) = 0
    rw [integral_sub (G j).integrable g.integrable, hG j, hg, sub_self]
  have hIG (j : ℕ) := (height_fractional_test_integrable_and_bound p μ f hf hweight (G j) (hG j)).1
  have hIg := (height_fractional_test_integrable_and_bound p μ f hf hweight g hg).1
  have hdiff (j : ℕ) : (∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) -
      (∫ x, f x • fractionalSchwartzTest p g x ∂μ) =
      ∫ x, f x • fractionalSchwartzTest p (H j) x ∂μ := by
    refine (integral_sub (hIG j) hIg).symm.trans (integral_congr_ae (Eventually.of_forall ?_))
    intro x
    calc
      _ = f x • (fractionalSchwartzTest p (G j) x - fractionalSchwartzTest p g x) :=
        (smul_sub (f x) (fractionalSchwartzTest p (G j) x) (fractionalSchwartzTest p g x)).symm
      _ = _ := congrArg (fun z : ℂ => f x • z)
        ((fractionalSchwartzTestCLM p x).map_sub (G j) g).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb (j : ℕ) :
      ‖(∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) -
        (∫ x, f x • fractionalSchwartzTest p g x ∂μ)‖ ≤
      fractionalSchwartzWeightedSize p (H j) *
        (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ) := by
    rw [hdiff j]
    exact (height_fractional_test_integrable_and_bound p μ f hf hweight (H j) (hHm j)).2
  apply squeeze_zero (fun j => norm_nonneg _) hb
  simpa only [zero_mul] using! (fractionalSchwartzWeightedSize_tendsto_zero p H hHt).mul_const
    (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ)

theorem height_fractional_test_zero_on_mean_zero_tests (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (hcompact : ∀ g : 𝓢(Ambient (p + 1), ℂ), HasCompactSupport g → (∫ y, g y) = 0 →
      (∫ x, f x • fractionalSchwartzTest p g x ∂μ) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ y, g y) = 0) :
    (∫ x, f x • fractionalSchwartzTest p g x ∂μ) = 0 := by
  obtain ⟨G, hG, ht⟩ := exists_compact_mean_zero_schwartz_approximation g hg
  have hlim := height_fractional_test_integral_tendsto p μ f hf hweight G g ht
    (fun j => (hG j).2) hg
  have hz : (fun j => ∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) =
      fun _ : ℕ => (0 : ℂ) := funext fun j => hcompact (G j) (hG j).1 (hG j).2
  rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end

end RieszRectifiability

end OAI
