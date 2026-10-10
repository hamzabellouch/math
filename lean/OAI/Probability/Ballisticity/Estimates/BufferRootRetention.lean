import Mathlib
import OAI.Probability.Ballisticity.Estimates.CountableProdBind

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferNodeAt_root_retained {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    {R : ℝ} (hR : 0 ≤ R) (a ε α g : ℝ) {κ : ℝ≥0}
    (hκpos : 0 < κ) (hκ1 : κ ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a)
    (l : List (ℕ × Bool)) (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u)
    (ha : ω ∈ (bufferNodeAt e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ H hH
      (bufferRootNode e f hef R a x hx) l).active) :
    ((κ:ℝ≥0∞)^(⌈R⌉₊+2)*(bufferRetentionCost R g κ)^l.length) •
      ((bufferNodeAt e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ H hH
        (bufferRootNode e f hef R a x hx) l).law ω).val ≤
      rawPairEndpointLaw (realPosition (step e)) (1+bufferWordHeight l) ω x := by
  let root := bufferRootNode e f hef R a x hx
  have hh := bufferNodeAt_retained e f hef hR (signedCoordinate f (x.2-x.1)) ε α g hκpos hκ1 hg hg1 hε hε1 hα
    H hH root le_rfl (bufferRootNode_valid e f hef R a x hx κ) l ω hκ ha
  have hs : (κ:ℝ≥0∞)^(⌈R⌉₊+2) • ((bufferRetentionCost R g κ)^l.length •
      ((bufferNodeAt e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ H hH root l).law ω).val) ≤
      (κ:ℝ≥0∞)^(⌈R⌉₊+2) • rawPairMixture (realPosition (step e)) (bufferWordHeight l) (root.law ω).val ω := by
    intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    have hhU := hh U
    simp only [Measure.smul_apply,smul_eq_mul] at hhU
    gcongr
  rw [←rawPairMixture_smul] at hs
  have hm := rawPairMixture_mono (realPosition (step e)) (bufferWordHeight l) ω
    (bufferRootNode_retained e f hef R a x hx ω hκ)
  have hf := hs.trans (hm.trans (rawPairEndpointLaw_comp_le e 1 (bufferWordHeight l) ω x))
  simpa only [smul_smul] using hf
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferStageRetainedLaw_baseline {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0)
    (hr : 0 ≤ r) (hε : ε ≤ 1) (hα : 0 ≤ α) :
    ∀ᵐ y ∂bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ,
      z₀ ≤ signedCoordinate f (y.2-y.1) := by
  by_cases hE : BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω
  · rw [bufferStageRetainedLaw_success e f a z₀ r ε α g π hH ω κ hE]
    filter_upwards [retainedPairLaw_support (realPosition (step e)) f H (z₀+(1+α)*r) (π ω).val ω] with y hy
    have : 0 ≤ (1+α)*r := by positivity
    linarith
  · filter_upwards [bufferStageRetainedLaw_failure_support e f a z₀ r ε α g π hH ω κ hE] with y hy
    have : 0 ≤ (1-ε)*r := mul_nonneg (sub_nonneg.mpr hε) hr
    linarith

lemma bufferPartialStage_mass {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) (hκ1 : κ ≤ 1) (hg1 : g ≤ 1)
    (hr : 0 ≤ r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    [IsProbabilityMeasure (π ω).val]
    (hgap : ∀ᵐ x ∂(π ω).val, z₀+r ≤ signedCoordinate f (x.2-x.1))
    (j : ℕ) (hj : j ≤ bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω) :
    (κ : ℝ≥0∞)^2*ENNReal.ofReal g ≤ pairKernelMass (realPosition (step e)) f j z₀ (π ω).val ω := by
  have hk1 : (κ:ℝ≥0∞) ≤ 1 := by exact_mod_cast hκ1
  have hc : (κ:ℝ≥0∞)^2*ENNReal.ofReal g ≤ ENNReal.ofReal g := by
    calc
      _ ≤ 1*ENNReal.ofReal g := by
        gcongr
        exact pow_le_one₀ (show (0:ℝ≥0∞) ≤ κ from zero_le) hk1
      _ = ENNReal.ofReal g := one_mul _
  by_cases hj0 : j=0
  · subst j
    rw [pairKernelMass_zero_of_supported]
    · exact hc.trans (by simpa using ENNReal.ofReal_le_ofReal hg1)
    · filter_upwards [hgap] with x hx
      linarith
  rcases lt_or_eq_of_le hj with hjlt|hjeq
  · have hp := before_bufferFirstFailure_pass (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω (Nat.pos_of_ne_zero hj0) hjlt
    apply hc.trans (hp.trans _)
    unfold pairKernelMass
    apply lintegral_mono
    intro x
    apply measure_mono
    intro y hy
    change z₀+(1-ε)*r ≤ signedCoordinate f (y.2-y.1) at hy
    change z₀ ≤ signedCoordinate f (y.2-y.1)
    have : 0 ≤ (1-ε)*r := mul_nonneg (sub_nonneg.mpr hε1) hr
    linarith
  · subst j
    let μ := bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ
    have hmass := bufferStageRetainedLaw_mass_lower e f a z₀ r ε α g π hH ω κ hκ1 hg1 hr hε hgap
    have hs := bufferStageRetainedLaw_baseline e f a z₀ r ε α g π hH ω κ hr hε1 hα
    have hm : μ Set.univ ≤ μ {y | z₀ ≤ signedCoordinate f (y.2-y.1)} := by
      apply measure_mono_ae
      filter_upwards [hs] with y hy
      exact fun _ => hy
    have hh := hmass.trans (hm.trans ((bufferStageRetainedLaw_le e f a z₀ r ε α g π hH ω hκ) _))
    simpa only [rawPairMixture_apply,pairKernelMass] using hh
end DirectionalTransience

end

end

end OAI
