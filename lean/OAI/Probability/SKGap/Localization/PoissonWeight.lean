import Mathlib
import OAI.Probability.SKGap.Localization.ThresholdChoice

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace SKGapCutoff

lemma totalVariation_mixture_le {n : ℕ} (w : Spin n → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (p : Spin n → Spin n → ℝ) (q : Spin n → ℝ) :
    totalVariation (fun y => ∑ x, w x*p x y) q ≤
      ∑ x, w x*totalVariation (p x) q := by
  unfold totalVariation
  have he y : (∑ x, w x*p x y)-q y = ∑ x, w x*(p x y-q y) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hs, one_mul]
  simp_rw [he]
  calc
    _ ≤ (∑ y, ∑ x, |w x*(p x y-q y)|)/2 := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      simp only [abs_mul, abs_of_nonneg (hw _)]
      rw [Finset.sum_comm]
      simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc]

lemma discreteKernel_add {n : ℕ} (J : Interaction n) (j k : ℕ) (x y : Spin n) :
    discreteKernel J (j+k) x y = ∑ z, discreteKernel J j x z*discreteKernel J k z y := by
  unfold discreteKernel
  rw [pow_add, mul_apply_eq_comp]
  exact (kernel_apply (attemptLM J ^ j) _ x).symm

lemma worstDiscrete_add_le {n : ℕ} (J : Interaction n) (j k : ℕ) :
    worstDiscrete J (j+k) ≤ worstDiscrete J k := by
  apply Finset.sup'_le
  intro x _
  change totalVariation (fun y => discreteKernel J (j+k) x y) (gibbs J) ≤ _
  simp_rw [discreteKernel_add]
  apply (totalVariation_mixture_le _ (discreteKernel_nonneg J j x)
    (discreteKernel_sum J j x) _ _).trans
  calc
    _ ≤ ∑ z, discreteKernel J j x z * worstDiscrete J k := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (discreteKernel_nonneg J j x z)
      exact Finset.le_sup' (fun z => totalVariation (discreteKernel J k z) (gibbs J)) (Finset.mem_univ z)
    _ = _ := by rw [← Finset.sum_mul, discreteKernel_sum, one_mul]

lemma worstDiscrete_antitone {n : ℕ} (J : Interaction n) :
    Antitone (worstDiscrete J) := by
  intro k j h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  exact worstDiscrete_add_le J d k

noncomputable def poissonWeight (r : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-r)*r^j/(j.factorial : ℝ)

lemma poissonWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (j : ℕ) :
    0 ≤ poissonWeight r j := by unfold poissonWeight; positivity

lemma poissonWeight_hasSum {r : ℝ} (hr : 0 ≤ r) : HasSum (poissonWeight r) 1 :=
  hasSum_one_poissonMeasure ⟨r,hr⟩

lemma poissonWeight_exp_hasSum (r s : ℝ) :
    HasSum (fun j => poissonWeight r j*Real.exp (s*(j:ℝ)))
      (Real.exp (r*(Real.exp s-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r*Real.exp s)).mul_left (Real.exp (-r))
  convert! h using 1
  · funext j
    rw [mul_pow, ← Real.exp_nat_mul]
    unfold poissonWeight
    ring_nf
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

lemma poisson_head_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k : ℕ) :
    (∑ j ∈ Finset.range k, poissonWeight r j) ≤
      Real.exp (s*(k:ℝ)+r*(Real.exp (-s)-1)) := by
  have hsum := (poissonWeight_exp_hasSum r (-s)).mul_left (Real.exp (s*k))
  have hle : (∑ j ∈ Finset.range k, poissonWeight r j) ≤
      ∑ j ∈ Finset.range k, Real.exp (s*k)*(poissonWeight r j*Real.exp (-s*j)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : (j:ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hj).le
    calc
      _ ≤ poissonWeight r j * Real.exp (s*((k:ℝ)-j)) := by
        exact le_mul_of_one_le_right (poissonWeight_nonneg hr j)
          ((Real.one_le_exp_iff).mpr (mul_nonneg hs (sub_nonneg.mpr hj')))
      _ = _ := by
        calc
          _ = poissonWeight r j * (Real.exp (s*k)*Real.exp (-s*j)) := by
            rw [← Real.exp_add]; congr 2; ring
          _ = _ := by ring
  apply hle.trans
  have ht := Summable.sum_le_tsum (Finset.range k) (fun j _ => by
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (poissonWeight_nonneg hr j) (Real.exp_pos _).le)) hsum.summable
  rw [hsum.tsum_eq] at ht
  simpa only [Real.exp_add] using ht

lemma continuousKernel_poisson_hasSum {n : ℕ} (hn : 0 < n)
    (J : Interaction n) (t : ℝ) (x y : Spin n) :
    HasSum (fun j => poissonWeight ((n:ℝ)*t) j * discreteKernel J j x y)
      (continuousKernel J t x y) := by
  have hs := (Pi.hasSum.mp
    (exp_apply_hasSum (((n:ℝ)*t) • attemptLM J)
      (fun z => if z = y then 1 else 0)) x).mul_left (Real.exp (-((n:ℝ)*t)))
  convert! hs using 1
  · funext j
    simp only [smul_pow, _root_.smul_apply, Pi.smul_apply, smul_eq_mul, discreteKernel, poissonWeight]
    ring
  · rw [continuousKernel, semigroup_uniformization hn]
    simp only [_root_.smul_apply, Pi.smul_apply, smul_eq_mul, neg_mul]

lemma continuousKernel_poisson_integral {n : ℕ} (hn : 0 < n)
    (J : Interaction n) (t : ℝ) (ht : 0 ≤ t) (x y : Spin n) :
    continuousKernel J t x y = ∫ j, discreteKernel J j x y
      ∂poissonMeasure (⟨(n:ℝ)*t, mul_nonneg (Nat.cast_nonneg n) ht⟩ : ℝ≥0) := by
  erw [integral_poissonMeasure]
  exact (continuousKernel_poisson_hasSum hn J t x y).tsum_eq.symm

lemma integrable_discreteKernel_poisson {n : ℕ} (J : Interaction n)
    (r : ℝ≥0) (x y : Spin n) : Integrable (fun j => discreteKernel J j x y) (poissonMeasure r) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (.of_discrete) (ae_of_all _ ?_)
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (discreteKernel_nonneg J j x y)]
  exact (Finset.single_le_sum (fun z _ => discreteKernel_nonneg J j x z)
    (Finset.mem_univ y)).trans_eq (discreteKernel_sum J j x)

lemma totalVariation_integral_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → Spin n → ℝ)
    (q : Spin n → ℝ) (hi : ∀ y, Integrable (fun j => p j y) μ) :
    totalVariation (fun y => ∫ j, p j y ∂μ) q ≤ ∫ j, totalVariation (p j) q ∂μ := by
  unfold totalVariation
  rw [integral_div, integral_finsetSum]
  swap
  · intro y _
    exact ((hi y).sub (integrable_const (q y))).abs
  gcongr with y
  have he : (∫ j, p j y ∂μ)-q y = ∫ j, (p j y-q y) ∂μ := by
    rw [integral_sub (hi y) (integrable_const _)]
    simp
  rw [he]
  exact abs_integral_le_integral_abs

lemma integrable_totalVariation_poisson {n : ℕ} (J : Interaction n)
    (r : ℝ≥0) (x : Spin n) :
    Integrable (fun j => totalVariation (discreteKernel J j x) (gibbs J)) (poissonMeasure r) := by
  unfold totalVariation
  apply Integrable.div_const
  apply integrable_finsetSum
  intro y _
  exact ((integrable_discreteKernel_poisson J r x y).sub (integrable_const _)).abs

lemma poisson_head_integral (r : ℝ≥0) (k : ℕ) :
    (∫ j : ℕ, (if j < k then (1:ℝ) else 0) ∂poissonMeasure r) =
      ∑ j ∈ Finset.range k, poissonWeight r j := by
  erw [integral_poissonMeasure]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_sum (s := Finset.range k) (fun j hj => by
    simp only [Finset.mem_range, not_lt] at hj
    simp only [not_lt.mpr hj, ite_false])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_left (Finset.mem_range.mp hj)]
  rfl

lemma continuous_le_poisson_head_add_discrete {n : ℕ} (hn : 0 < n)
    (J : Interaction n) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    worstContinuous J t ≤ (∑ j ∈ Finset.range k, poissonWeight ((n:ℝ)*t) j) +
      worstDiscrete J k := by
  let r : ℝ≥0 := ⟨(n:ℝ)*t,mul_nonneg (Nat.cast_nonneg n) ht⟩
  apply Finset.sup'_le
  intro x _
  change totalVariation (continuousKernel J t x) (gibbs J) ≤ _
  have he : continuousKernel J t x = fun y => ∫ j, discreteKernel J j x y ∂poissonMeasure r := by
    funext y
    exact continuousKernel_poisson_integral hn J t ht x y
  rw [he]
  apply (totalVariation_integral_le _ _ _ (integrable_discreteKernel_poisson J r x)).trans
  have hbi : Integrable (fun j : ℕ => if j < k then (1:ℝ) else 0) (poissonMeasure r) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) (.of_discrete)
    exact ae_of_all _ (fun j => by split_ifs <;> norm_num)
  calc
    _ ≤ ∫ j : ℕ, (if j < k then (1:ℝ) else 0)+worstDiscrete J k ∂poissonMeasure r := by
      apply integral_mono (integrable_totalVariation_poisson J r x)
        (hbi.add (integrable_const _))
      intro j
      change totalVariation (discreteKernel J j x) (gibbs J) ≤
        (if j < k then (1:ℝ) else 0)+worstDiscrete J k
      by_cases hj : j < k
      · simp only [ite_eq_left hj]
        have hb := totalVariation_le_one _ _ (discreteKernel_nonneg J j x)
          (fun y => (gibbs_pos J y).le) (discreteKernel_sum J j x) (gibbs_sum J)
        linarith [worstDiscrete_nonneg J k]
      · simp only [ite_eq_right hj, zero_add]
        apply (Finset.le_sup' (fun x => totalVariation (discreteKernel J j x) (gibbs J))
          (Finset.mem_univ x)).trans
        exact worstDiscrete_antitone J (not_lt.mp hj)
    _ = _ := by
      rw [integral_add hbi (integrable_const _), poisson_head_integral]
      have hu : (poissonMeasure r).real Set.univ = 1 := by
        simp [Measure.real, measure_univ]
      simp only [integral_const, smul_eq_mul, hu, one_mul]
      rfl

lemma exists_poisson_head_exponent {a : ℝ} (_ha : 0 ≤ a) (ha1 : a < 1) :
    ∃ s c : ℝ, 0 < s ∧ 0 < c ∧ s*a+Real.exp (-s)-1 = -c := by
  let s := (1-a)/2
  have hs : 0 < s := by dsimp [s]; linarith
  have he : Real.exp (-s) ≤ (1+s)⁻¹ := by
    rw [Real.exp_neg]
    simp only [← one_div]
    apply one_div_le_one_div_of_le (by linarith : 0 < 1+s)
    linarith [Real.add_one_le_exp s]
  have ha' : a*(1+s) < 1 := by
    have hm := mul_le_mul_of_nonneg_right ha1.le hs.le
    dsimp [s] at *
    nlinarith
  have hh : s*a+(1+s)⁻¹-1 < 0 := by
    have hpos : 0 < 1+s := by linarith
    have hid : (s*a+(1+s)⁻¹-1)*(1+s) = s*(a*(1+s)-1) := by
      field_simp
      ring
    have hp := mul_neg_of_pos_of_neg hs (sub_neg.mpr ha')
    rw [← hid] at hp
    nlinarith
  refine ⟨s, -(s*a+Real.exp (-s)-1),hs,?_,by ring⟩
  linarith

lemma poisson_head_tendsto_zero {r : ℕ → ℝ} {k : ℕ → ℕ} {a : ℝ}
    (hr : Tendsto r atTop atTop) (ha : 0 ≤ a) (ha1 : a < 1)
    (hkr : ∀ᶠ n in atTop, 0 ≤ r n ∧ (k n : ℝ) ≤ a*r n) :
    Tendsto (fun n => ∑ j ∈ Finset.range (k n), poissonWeight (r n) j) atTop (𝓝 0) := by
  obtain ⟨s,c,hs,hc,he⟩ := exists_poisson_head_exponent ha ha1
  have hh : Tendsto (fun n => Real.exp (-c*r n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hr.const_mul_atTop hc)
  apply tendsto_const_nhds.squeeze' hh
  · filter_upwards [hkr] with n hn
    exact Finset.sum_nonneg (fun j _ => poissonWeight_nonneg hn.1 j)
  · filter_upwards [hkr] with n hn
    apply (poisson_head_le hn.1 hs.le (k n)).trans
    apply Real.exp_le_exp.mpr
    calc
      s*(k n:ℝ)+r n*(Real.exp (-s)-1) ≤ s*(a*r n)+r n*(Real.exp (-s)-1) := by
        gcongr
        exact hn.2
      _ = (s*a+Real.exp (-s)-1)*r n := by ring
      _ = -c*r n := by rw [he]

lemma disorderLimit_one_of_clock_transfer {β : ℝ}
    {F G : (n : ℕ) → Interaction n → ℝ} {e : ℕ → ℝ}
    (hF : DisorderLimit β F 1) (he : Tendsto e atTop (𝓝 0))
    (hcomp : ∀ᶠ n in atTop, ∀ J, G n J ≤ 1 ∧ F n J ≤ e n+G n J) :
    DisorderLimit β G 1 := by
  intro δ hδ
  apply tendsto_const_nhds.squeeze' (hF (δ/2) (by positivity))
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hcomp, he.eventually (gt_mem_nhds (by linarith : 0 < δ/2))] with n hn hen
  apply measure_mono
  intro g hg
  obtain ⟨hG,hFG⟩ := hn (sampledInteraction g)
  change δ < |G n (sampledInteraction g)-1| at hg
  rw [abs_of_nonpos (sub_nonpos.mpr hG)] at hg
  have hh := neg_le_abs (F n (sampledInteraction g)-1)
  change δ/2 < |F n (sampledInteraction g)-1|
  linarith

lemma cutoffTime_tendsto_atTop {rate : ℝ} (hrate : 0 < rate) :
    Tendsto (cutoffTime rate) atTop atTop := by
  change Tendsto (fun n : ℕ => Real.log (n:ℝ)/(2*rate)) atTop atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [div_eq_mul_inv] using hlog.atTop_mul_const
    (inv_pos.mpr (by positivity : 0 < 2*rate))

theorem discrete_lower_from_continuous {β rate ε : ℝ} (hrate : 0 < rate)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hcont : DisorderLimit β
      (fun n J => worstContinuous J ((1-ε/2)*cutoffTime rate n)) 1) :
    DisorderLimit β (fun n J => worstDiscrete J
      ⌊(1-ε)*(n:ℝ)*cutoffTime rate n⌋₊) 1 := by
  let r : ℕ → ℝ := fun n => (n:ℝ)*((1-ε/2)*cutoffTime rate n)
  let k : ℕ → ℕ := fun n => ⌊(1-ε)*(n:ℝ)*cutoffTime rate n⌋₊
  let a : ℝ := (1-ε)/(1-ε/2)
  have hmid : 0 < 1-ε/2 := by linarith
  have ha : 0 ≤ a := div_nonneg (by linarith) hmid.le
  have ha1 : a < 1 := by
    apply (div_lt_one hmid).mpr
    linarith
  have hr : Tendsto r atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).atTop_mul_atTop₀
      ((cutoffTime_tendsto_atTop hrate).const_mul_atTop hmid)
  have hkr : ∀ᶠ n in atTop, 0 ≤ r n ∧ (k n:ℝ) ≤ a*r n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have ht := cutoffTime_nonneg hn hrate
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hmid.le ht)
    · apply (Nat.floor_le (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) ht)).trans
      dsimp [a,r]
      apply le_of_eq
      have hne : (2-ε) ≠ 0 := by linarith
      field_simp [hne]
  apply disorderLimit_one_of_clock_transfer hcont (poisson_head_tendsto_zero hr ha ha1 hkr)
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro J
  exact ⟨worstDiscrete_le_one J _, continuous_le_poisson_head_add_discrete hn J _
    (mul_nonneg hmid.le (cutoffTime_nonneg hn hrate)) _⟩

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

end

end OAI
