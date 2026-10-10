import Mathlib
import OAI.Probability.Ballisticity.Estimates.SymmetricPrefixTail

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma iid_fluctuation_not_collapse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ)
    (hid : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (k : ℕ → ℕ)
    {τ : ℝ} (hτ : 0 < τ)
    (hk : Tendsto (fun i => (k i:ℝ)/fluctuationScale μ (X 0) (r i)) atTop (𝓝 τ))
    (hcollapse : TendstoInMeasure μ
      (fun i ω => realPartialSum (fun j => X j ω) (k i)/r i) atTop 0) : False := by
  have hg := gaussian_sequence_of_collapsed_sums μ X hX hind hid hsym hI hne r hr k hτ hk (fun a ha => ?_)
  · have hcf := gaussian_charFun_power_limit_count μ (X 0) (hX 0) hI hne hsym r hg k hk 1
    have hd := hcollapse.tendstoInDistribution (fun i => by unfold realPartialSum; fun_prop)
    have hc := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hd.tendsto 1
    change Tendsto (fun i => charFun (μ.map (fun ω => realPartialSum (fun j => X j ω) (k i)/r i)) 1)
      atTop (𝓝 (charFun (μ.map (fun _ : Ω => (0:ℝ))) 1)) at hc
    simp only [charFun_div_partialSum μ X hind hid,Measure.map_const,measure_univ,one_smul,
      charFun_dirac,inner_zero_left,Complex.ofReal_zero,zero_mul,Complex.exp_zero] at hc
    have he := tendsto_nhds_unique hcf hc
    have he' := congrArg Complex.re he
    simp only [one_pow,mul_one,←Complex.ofReal_neg,←Complex.ofReal_exp,Complex.ofReal_re,Complex.one_re] at he'
    have hh : Real.exp (-(τ/2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact hh.ne he'
  · have hc := tendstoInMeasure_iff_measureReal_norm.mp hcollapse a ha
    simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at hc
    apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hc
    filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ))] with i hi
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    change a*r i < |realPartialSum (fun j => X j ω) (k i)| at hω
    change a ≤ |realPartialSum (fun j => X j ω) (k i)/r i|
    rw [abs_div,abs_of_pos hi,le_div_iff₀ hi]
    exact hω.le
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma double_floor_ratio (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun i => (⌊(⌊n i⌋₊:ℝ)/c⌋₊:ℝ)/n i) atTop (𝓝 (1/c)) := by
  have hH : Tendsto (fun i => (⌊n i⌋₊:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp hn)
  have hin : Tendsto (fun i => (⌊n i⌋₊:ℝ)/n i) atTop (𝓝 1) := by
    simpa only [one_mul,Function.comp_def] using (tendsto_nat_floor_mul_div_atTop (show (0:ℝ)≤1 by norm_num)).comp hn
  have hout : Tendsto (fun i => (⌊(⌊n i⌋₊:ℝ)/c⌋₊:ℝ)/(⌊n i⌋₊:ℝ)) atTop (𝓝 (1/c)) := by
    simpa only [Function.comp_def,one_div,one_mul,mul_comm c⁻¹,div_eq_mul_inv] using
      (tendsto_nat_floor_mul_div_atTop (show 0 ≤ 1/c by positivity)).comp hH
  have hh := hout.mul hin
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [hH.eventually (eventually_gt_atTop (0:ℝ))] with i hi
  exact div_mul_div_cancel₀ (ne_of_gt hi)
lemma inMeasure_sub_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : ℕ → Ω → ℝ) (hF : TendstoInMeasure μ F atTop 0)
    (hG : TendstoInMeasure μ G atTop 0) :
    TendstoInMeasure μ (fun i ω => F i ω-G i ω) atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have hf := tendstoInMeasure_iff_measureReal_norm.mp hF (ε/2) (by positivity)
  have hg := tendstoInMeasure_iff_measureReal_norm.mp hG (ε/2) (by positivity)
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at hf hg ⊢
  apply squeeze_zero (fun i => measureReal_nonneg) _ (by simpa only [add_zero] using hf.add hg)
  intro i
  apply (measureReal_mono (μ := μ) _).trans (measureReal_union_le _ _)
  intro ω hω
  change ε ≤ |F i ω-G i ω| at hω
  change ε/2 ≤ |F i ω| ∨ ε/2 ≤ |G i ω|
  by_contra! hn
  have hh := norm_sub_le (F i ω) (G i ω)
  simp only [Real.norm_eq_abs] at hh
  linarith
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def dyadicCut (j : ℕ) : ℝ := (1/2)^j
lemma dyadicCut_pos (j : ℕ) : 0 < dyadicCut j := pow_pos (by norm_num) _
lemma dyadicCut_le_one (j : ℕ) : dyadicCut j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
lemma dyadicCut_antitone : Antitone dyadicCut := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
lemma dyadicCut_tendsto : Tendsto dyadicCut atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma variance_ratio_unit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    truncatedVariance μ S (a*r)/truncatedVariance μ S r ∈ Icc (0:ℝ) 1 := by
  have hp := truncatedVariance_pos μ S hS hne hr
  constructor
  · exact div_nonneg (truncatedVariance_nonneg _ _ _) hp.le
  · rw [div_le_one hp]
    apply truncatedVariance_mono μ S hS (mul_nonneg ha hr.le)
    nlinarith

lemma exists_dyadic_variance_profile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∃ (ns : ℕ → ℕ) (F : ℕ → ℝ) (F₀ : ℝ), StrictMono ns ∧
      (∀ j, Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r (ns n))/truncatedVariance μ S (r (ns n))) atTop (𝓝 (F j))) ∧
      (∀ j, F j ∈ Icc (0:ℝ) 1) ∧ F 0 = 1 ∧ Antitone F ∧
      F₀ ∈ Icc (0:ℝ) 1 ∧ Tendsto F atTop (𝓝 F₀) ∧ (∀ j, F₀ ≤ F j) := by
  let R : ℕ → ℕ → Icc (0:ℝ) 1 := fun n j =>
    ⟨truncatedVariance μ S (dyadicCut j*r n)/truncatedVariance μ S (r n),
      variance_ratio_unit μ S hS hne (hr n) (dyadicCut_pos j).le (dyadicCut_le_one j)⟩
  obtain ⟨f,ns,hns,hlim⟩ := CompactSpace.tendsto_subseq R
  let F := fun j => (f j:ℝ)
  have hF (j) : Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r (ns n))/truncatedVariance μ S (r (ns n))) atTop (𝓝 (F j)) :=
    continuous_subtype_val.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hlim) j)
  have hbounds (j) : F j ∈ Icc (0:ℝ) 1 := (f j).property
  have hFone : F 0 = 1 := by
    have heq : (fun n => truncatedVariance μ S (dyadicCut 0*r (ns n))/truncatedVariance μ S (r (ns n))) = fun _ => (1:ℝ) := by
      funext n
      simp only [dyadicCut,pow_zero,one_mul]
      exact div_self (ne_of_gt (truncatedVariance_pos μ S hS hne (hr (ns n))))
    exact tendsto_nhds_unique (heq ▸ hF 0) tendsto_const_nhds
  have hanti : Antitone F := by
    intro i j hij
    apply le_of_tendsto_of_tendsto (hF j) (hF i)
    exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (truncatedVariance_mono μ S hS (mul_nonneg (dyadicCut_pos j).le (hr (ns n)).le)
        (mul_le_mul_of_nonneg_right (dyadicCut_antitone hij) (hr (ns n)).le))
      (truncatedVariance_nonneg μ S _)
  have hb : BddBelow (range F) := ⟨0,fun x ⟨j,hj⟩ => hj ▸ (hbounds j).1⟩
  have hlimF : Tendsto F atTop (𝓝 (⨅ j, F j)) := tendsto_atTop_ciInf hanti hb
  have hinf0 : 0 ≤ ⨅ j, F j := le_ciInf (fun j => (hbounds j).1)
  have hinfj (j) : (⨅ i, F i) ≤ F j := ciInf_le hb j
  exact ⟨ns,F,⨅ j, F j,hns,hF,hbounds,hFone,hanti,⟨hinf0,(hinfj 0).trans (hbounds 0).2⟩,hlimF,hinfj⟩

end DirectionalTransience

end

end

end OAI
