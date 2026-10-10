import OAI.Analysis.CircleDomains.Sobolev.BoundedContinuousL2Dual
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! Positivity of an L² function is detected by nonnegative bounded continuous
functions. The extension to L² uses continuity of the actual positive part. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma boundedContinuous_toLp_posPart
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] (f : Z →ᵇ ℝ) :
    BoundedContinuousFunction.toLp 2 σ ℝ f⁺ =
      Lp.posPart (BoundedContinuousFunction.toLp 2 σ ℝ f) := by
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f⁺,
    BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f,
    Lp.coeFn_posPart (BoundedContinuousFunction.toLp 2 σ ℝ f)] with z hp hf hq
  rw [hp,hq,hf]
  rfl

lemma L2_nonneg_of_boundedContinuous_tests
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [NormalSpace Z] [SecondCountableTopology Z]
    (σ : Measure Z) [IsFiniteMeasure σ] [σ.WeaklyRegular]
    (g : Lp ℝ 2 σ)
    (hg : ∀ f : Z →ᵇ ℝ, (∀ z, 0 ≤ f z) → 0 ≤ ∫ z, g z * f z ∂σ) :
    ∀ᵐ z ∂σ, 0 ≤ g z := by
  have hpos (v : Lp ℝ 2 σ) : 0 ≤ inner ℝ g (Lp.posPart v) := by
    refine (BoundedContinuousFunction.toLp_denseRange ℝ σ ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).induction_on v ?_ ?_
    · exact isClosed_le continuous_const (continuous_const.inner Lp.continuous_posPart)
    · intro f
      rw [← boundedContinuous_toLp_posPart σ f, L2.inner_def]
      have heq : (∫ z, inner ℝ (g z)
          (BoundedContinuousFunction.toLp 2 σ ℝ f⁺ z) ∂σ) =
          ∫ z, g z * (f⁺) z ∂σ := by
        apply integral_congr_ae
        filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f⁺] with z hz
        simp only [hz,Real.inner_apply]
      rw [heq]
      apply hg
      intro z
      change 0 ≤ max (f z) 0
      exact le_max_right _ _
  let n : Lp ℝ 2 σ := Lp.negPart g
  have hn : inner ℝ g n = - inner ℝ n n := by
    rw [L2.inner_def,L2.inner_def,← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_negPart_eq_max g] with z hz
    change n z = max (-g z) 0 at hz
    simp only [Real.inner_apply]
    rcases le_total 0 (g z) with h | h
    · rw [max_eq_right (neg_nonpos.mpr h)] at hz
      rw [hz]
      ring
    · rw [max_eq_left (neg_nonneg.mpr h)] at hz
      rw [hz]
      ring
  have hz : n = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hp : 0 ≤ inner ℝ g n := hpos (-g)
    have hnn : 0 ≤ inner ℝ n n := real_inner_self_nonneg
    linarith
  filter_upwards [Lp.coeFn_negPart_eq_max g, Lp.coeFn_zero ℝ 2 σ] with z hn hzero
  change n z = max (-g z) 0 at hn
  rw [hz,hzero] at hn
  have h := le_max_left (-g z) 0
  rw [← hn] at h
  change -g z ≤ 0 at h
  linarith

end CircleDomainRigidity

end

end OAI
