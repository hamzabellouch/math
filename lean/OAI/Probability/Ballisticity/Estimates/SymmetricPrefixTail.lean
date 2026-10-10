import Mathlib
import OAI.Probability.Ballisticity.Estimates.MeasureAdd

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma symmetric_iid_partialSum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ)
    (hsym : ∀ j, IdentDistrib (X j) (fun ω => -X j ω) μ μ) (n : ℕ) :
    IdentDistrib (fun ω => realPartialSum (fun j => X j ω) n)
      (fun ω => -realPartialSum (fun j => X j ω) n) μ μ := by
  induction n with
  | zero => simp only [realPartialSum,Finset.range_zero,Finset.sum_empty,neg_zero]; exact IdentDistrib.refl measurable_const.aemeasurable
  | succ n ih =>
    have hi : IndepFun (fun ω => realPartialSum (fun j => X j ω) n) (X n) μ := by
      have he : (∑ j ∈ Finset.range n, X j) = (fun ω => realPartialSum (fun j => X j ω) n) := by
        funext ω
        simp only [realPartialSum,Finset.sum_apply]
      rw [←he]
      exact hind.indepFun_finsetSum_of_notMem hX (show n ∉ Finset.range n by simp)
    have hin := hi.comp measurable_neg measurable_neg
    have hh := (ih.prodMk (hsym n) hi hin).comp measurable_add
    simpa only [Function.comp_def,realPartialSum,Finset.sum_range_succ,neg_add] using hh

lemma independent_prefix_remainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ) (m n : ℕ) :
    IndepFun (fun ω => realPartialSum (fun j => X j ω) m)
      (fun ω => ∑ j ∈ Finset.Ico m n, X j ω) μ := by
  have hd : Disjoint (Finset.range m) (Finset.Ico m n) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_range,Finset.mem_Ico] at hj hk
    omega
  have hi := hind.indepFun_finset (Finset.range m) (Finset.Ico m n) hd hX
  have hh := hi.comp (show Measurable (fun z : Finset.range m → ℝ => ∑ j, z j) by fun_prop)
    (show Measurable (fun z : Finset.Ico m n → ℝ => ∑ j, z j) by fun_prop)
  change IndepFun (fun ω => ∑ j : Finset.range m, X j.1 ω)
    (fun ω => ∑ j : Finset.Ico m n, X j.1 ω) μ at hh
  have he (ω : Ω) : (∑ j : Finset.range m, X j.1 ω) = realPartialSum (fun j => X j ω) m := by
    exact Finset.sum_coe_sort (Finset.range m) (fun j => X j ω)
  have hf (ω : Ω) : (∑ j : Finset.Ico m n, X j.1 ω) = ∑ j ∈ Finset.Ico m n, X j ω := by
    exact Finset.sum_coe_sort (Finset.Ico m n) (fun j => X j ω)
  simpa only [he,hf] using hh

lemma symmetric_prefix_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ)
    (hsym : ∀ j, IdentDistrib (X j) (fun ω => -X j ω) μ μ)
    {m n : ℕ} (hmn : m ≤ n) (a : ℝ) :
    (1/2:ℝ)*μ.real {ω | a < |realPartialSum (fun j => X j ω) m|} ≤
      μ.real {ω | a < |realPartialSum (fun j => X j ω) n|} := by
  have hh := symmetric_summand_tail μ
    (fun ω => realPartialSum (fun j => X j ω) m) (fun ω => ∑ j ∈ Finset.Ico m n, X j ω)
    (by unfold realPartialSum; fun_prop) (by fun_prop) (symmetric_iid_partialSum μ X hX hind hsym m)
    (independent_prefix_remainder μ X hX hind m n) a
  have he (ω) : realPartialSum (fun j => X j ω) m + ∑ j ∈ Finset.Ico m n, X j ω =
      realPartialSum (fun j => X j ω) n := Finset.sum_range_add_sum_Ico _ hmn
  simp only [he] at hh
  exact hh.trans (measureReal_mono fun _ h => h.2)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma gaussian_sequence_of_collapsed_sums {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ)
    (hid : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (k : ℕ → ℕ)
    {τ : ℝ} (hτ : 0 < τ)
    (hk : Tendsto (fun i => (k i:ℝ)/fluctuationScale μ (X 0) (r i)) atTop (𝓝 τ))
    (hcollapse : ∀ a : ℝ, 0 < a → Tendsto
      (fun i => μ.real {ω | a*r i < |realPartialSum (fun j => X j ω) (k i)|}) atTop (𝓝 0)) :
    IsGaussianSequence μ (X 0) r := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr
  have hsymj (j) : IdentDistrib (X j) (fun ω => -X j ω) μ μ :=
    (hid j).trans (hsym.trans ((hid j).symm.comp measurable_neg))
  refine ⟨hr,fun a ha => ?_⟩
  let l := min a 1
  have hl : 0 < l := lt_min ha zero_lt_one
  have hl1 : l ≤ 1 := min_le_right _ _
  have hla : l ≤ a := min_le_left _ _
  let t := min (τ/4) (l^2/4)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htτ : t ≤ τ/4 := min_le_left _ _
  have htl : t ≤ l^2/4 := min_le_right _ _
  let m := fun i => ⌊t*n i⌋₊
  let p := fun i => μ.real {ω | l*r i < |X 0 ω|}
  have hbd : ∀ᶠ i in atTop, n i*μ.real {ω | a*r i < |X 0 ω|} ≤
      (16/t)*μ.real {ω | l*r i < |realPartialSum (fun j => X j ω) (k i)|} := by
    filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ)),
      hn.eventually (eventually_ge_atTop (2/t)),hk.eventually (lt_mem_nhds (show τ/2 < τ by linarith))] with i hri hni hki
    have hn0 : 0 < n i := (div_pos (by norm_num : (0:ℝ)<2) ht).trans_le hni
    have hnp : n i*p i ≤ 1/l^2 := fluctuation_tail_bound μ (X 0) (hX 0) hne hri hl hl1
    have hp0 : 0 ≤ p i := measureReal_nonneg
    have hmhi : (m i:ℝ) ≤ t*n i := Nat.floor_le (mul_nonneg ht.le hn0.le)
    have hmlo : t*n i/2 ≤ (m i:ℝ) := by
      have hh := Nat.lt_floor_add_one (t*n i)
      have hni' := (div_le_iff₀ ht).mp hni
      dsimp [m]
      nlinarith
    have hmk : m i ≤ k i := by
      have hki' : τ/2*n i < (k i:ℝ) := (lt_div_iff₀ hn0).mp hki
      exact_mod_cast (show (m i:ℝ) ≤ (k i:ℝ) by nlinarith)
    have hu0 : 0 ≤ (m i:ℝ)*p i := mul_nonneg (Nat.cast_nonneg _) hp0
    have hu1 : (m i:ℝ)*p i ≤ 1/4 := by
      have hh := mul_le_mul_of_nonneg_left hnp ht.le
      rw [mul_one_div] at hh
      have hh' := mul_le_mul_of_nonneg_right hmhi hp0
      have hfrac : t/l^2 ≤ 1/4 := (div_le_iff₀ (sq_pos_of_pos hl)).mpr (by nlinarith only [htl])
      nlinarith
    have hra := iid_symmetric_sum_spread μ X hX hind hid hsym (l*r i) (m i)
    have hpre := symmetric_prefix_tail μ X hX hind hsymj hmk (l*r i)
    change (1/2:ℝ)*((m i:ℝ)*p i)-((m i:ℝ)*p i)^2/2 ≤
      μ.real {ω | l*r i < |realPartialSum (fun j => X j ω) (m i)|} at hra
    have hu : ((m i:ℝ)*p i)/4 ≤
      μ.real {ω | l*r i < |realPartialSum (fun j => X j ω) (m i)|} := by
      nlinarith only [hra,hu0,hu1,mul_nonneg hu0 (show 0 ≤ 1/2-(m i:ℝ)*p i by linarith)]
    have hpa : μ.real {ω | a*r i < |X 0 ω|} ≤ p i :=
      measureReal_mono (fun ω hω => (mul_le_mul_of_nonneg_right hla hri.le).trans_lt hω)
    have hscale := mul_le_mul_of_nonneg_right hmlo hp0
    have hfinal : t*(n i*p i) ≤ 16*μ.real {ω | l*r i < |realPartialSum (fun j => X j ω) (k i)|} := by
      nlinarith only [hu,hpre,hscale]
    have hh : n i*p i ≤ (16/t)*μ.real {ω | l*r i < |realPartialSum (fun j => X j ω) (k i)|} := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ ht).2 (by nlinarith only [hfinal])
    exact (mul_le_mul_of_nonneg_left hpa hn0.le).trans hh
  apply squeeze_zero' (Eventually.of_forall fun i => mul_nonneg (fluctuationScale_nonneg _ _ _) measureReal_nonneg) hbd
  simpa using (hcollapse l hl).const_mul (16/t)
end DirectionalTransience

end

end

end OAI
