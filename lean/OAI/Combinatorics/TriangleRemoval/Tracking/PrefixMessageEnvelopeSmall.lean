import Mathlib
import OAI.Combinatorics.TriangleRemoval.Stability.CavityReference

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma prefix_message_envelope_small {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ 12*prefixHorizon n/prefixD n ∧
      12*prefixHorizon n/prefixD n ≤ b := by
  have hpoly := prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/1000)
    (div_pos hb (by norm_num : (0 : ℝ) < 12))
  filter_upwards [prefixHorizon_bounds,prefixD_eventual_envelope,
    prefix_scales_eventually_pos,hpoly] with n hS hD hp hpoly
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  have hpoly' : 1+Real.log n ≤ (b/12)*(n : ℝ)^(1/1000 : ℝ) := by
    simpa only [prefixTemplateFactor,Real.rpow_one] using hpoly
  refine ⟨div_nonneg (mul_nonneg (by norm_num) hS.1.le) hD0.le,?_⟩
  apply (div_le_iff₀ hD0).mpr
  have hbound := mul_le_mul_of_nonneg_left hD.1 hb.le
  nlinarith [hS.2]

lemma prefix_message_envelope_tendsto :
    Tendsto (fun n : ℕ => 12*prefixHorizon n/prefixD n) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [prefix_message_envelope_small zero_lt_one] with n hn
    exact ha.trans_le hn.1
  · intro b hb
    filter_upwards [prefix_message_envelope_small (show 0 < b/2 by linarith)] with n hn
    exact hn.2.trans_lt (by linarith)

theorem goodPrefix_cavity_stability {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ e : G, |cavityLimit (activeHypergraph G) e none t /
            cavityReference (prefixD n) t - 1| ≤ ε) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          |cavityLimit (activeHypergraph G) e (some T) t /
            cavityReference (prefixD n) t - 1| ≤ ε) := by
  obtain ⟨a,ha,hrel⟩ := goodPrefix_cavity_relative hc
  have hδ := (tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlo : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ)^(-a)/2)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp (hδ.neg.div_const 2)
  have hexp : Tendsto (fun n : ℕ => Real.exp ((n : ℝ)^(-a)/2)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp (hδ.div_const 2)
  have hden : Tendsto (fun n : ℕ => 1-12*prefixHorizon n/prefixD n) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub prefix_message_envelope_tendsto
  have hhi : Tendsto (fun n : ℕ => Real.exp ((n : ℝ)^(-a)/2)/
      (1-12*prefixHorizon n/prefixD n)) atTop (𝓝 1) := by
    simpa only [Pi.div_def,div_one] using hexp.div hden one_ne_zero
  filter_upwards [hrel,hlo.eventually_const_le (by linarith : 1-ε < 1),
    hhi.eventually_le_const (by linarith : 1 < 1+ε),
    hexp.eventually_le_const (by linarith : 1 < 1+ε)] with n hrel hlo hhi hexp
  intro C G h t ht
  obtain ⟨hroot,hparent⟩ := hrel.2 C G h t ht
  constructor
  · intro e
    apply abs_le.mpr
    obtain ⟨he1,he2⟩ := hroot e
    constructor <;> linarith
  · intro e T he
    obtain ⟨_,he1,he2⟩ := hparent e T he
    apply abs_le.mpr
    constructor <;> linarith

end SharpTerminalLeave

open scoped BigOperators

end

end OAI
