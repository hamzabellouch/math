import Mathlib
import OAI.Probability.SKRatio.Dynamics.Median
import OAI.Probability.SKRatio.Dynamics.LogQuadratic

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory SKRatioClock
namespace SKRatio.Calculus

lemma poissonMass_nonneg {r : ℝ} (hr : 0 ≤ r) (j : ℕ) :
    0 ≤ Clock.poissonMass r j := by unfold Clock.poissonMass; positivity

lemma poissonMass_exp_hasSum (r s : ℝ) :
    HasSum (fun j => Clock.poissonMass r j*Real.exp (s*(j:ℝ)))
      (Real.exp (r*(Real.exp s-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r*Real.exp s)).mul_left (Real.exp (-r))
  convert! h using 1
  · funext j
    rw [mul_pow, ← Real.exp_nat_mul]
    unfold Clock.poissonMass
    ring_nf
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

lemma poisson_head_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (k : ℕ) :
    (∑ j ∈ Finset.range k, Clock.poissonMass r j) ≤
      Real.exp (s*(k:ℝ)+r*(Real.exp (-s)-1)) := by
  have hsum := (poissonMass_exp_hasSum r (-s)).mul_left (Real.exp (s*k))
  have hle : (∑ j ∈ Finset.range k, Clock.poissonMass r j) ≤
      ∑ j ∈ Finset.range k, Real.exp (s*k)*(Clock.poissonMass r j*Real.exp (-s*j)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : (j:ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hj).le
    calc
      _ ≤ Clock.poissonMass r j * Real.exp (s*((k:ℝ)-j)) := by
        exact le_mul_of_one_le_right (poissonMass_nonneg hr j)
          ((Real.one_le_exp_iff).mpr (mul_nonneg hs (sub_nonneg.mpr hj')))
      _ = _ := by
        calc
          _ = Clock.poissonMass r j * (Real.exp (s*k)*Real.exp (-s*j)) := by
            rw [← Real.exp_add]; congr 2; ring
          _ = _ := by ring
  apply hle.trans
  have ht := Summable.sum_le_tsum (Finset.range k) (fun j _ => by
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (poissonMass_nonneg hr j) (Real.exp_pos _).le)) hsum.summable
  rw [hsum.tsum_eq] at ht
  simpa only [Real.exp_add] using ht

lemma exists_poisson_head_exponent {a : ℝ} (ha1 : a < 1) :
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

lemma continuousKernel_poisson_integral {n : ℕ} (hn : 0 < n)
    (g : Disorder n) (t : ℝ) (ht : 0 ≤ t) (x y : Spin n) :
    continuousKernel (coupling g) t x y = ∫ j, (transition g ^ j) x y
      ∂poissonMeasure (⟨(n:ℝ)*t, mul_nonneg (Nat.cast_nonneg n) ht⟩ : ℝ≥0) := by
  erw [integral_poissonMeasure]
  change continuousKernel (coupling g) t x y =
    ∑' j, Real.exp (-((n:ℝ)*t))*((n:ℝ)*t)^j/(j.factorial:ℝ)*(transition g ^ j) x y
  simpa only [neg_mul] using
    (continuousKernel_poisson_hasSum hn g t x y).tsum_eq.symm

lemma integrable_discreteKernel_poisson {n : ℕ} (g : Disorder n)
    (r : ℝ≥0) (x y : Spin n) :
    Integrable (fun j => (transition g ^ j) x y) (poissonMeasure r) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (.of_discrete) (ae_of_all _ ?_)
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg ((transition_pow_stochastic g j).1 x y)]
  exact (Finset.single_le_sum (fun z _ => (transition_pow_stochastic g j).1 x z)
    (Finset.mem_univ y)).trans_eq
    (Matrix.sum_row_of_mem_rowStochastic (transition_pow_stochastic g j) x)

lemma totalVariation_integral_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → Spin n → ℝ)
    (q : Spin n → ℝ) (hi : ∀ y, Integrable (fun j => p j y) μ) :
    totalVariation (fun y => ∫ j, p j y ∂μ) q ≤ ∫ j, totalVariation (p j) q ∂μ := by
  unfold totalVariation
  rw [integral_const_mul, integral_finsetSum]
  swap
  · intro y _
    exact ((hi y).sub (integrable_const (q y))).abs
  gcongr with y
  have he : (∫ j, p j y ∂μ)-q y = ∫ j, (p j y-q y) ∂μ := by
    rw [integral_sub (hi y) (integrable_const _)]
    simp
  rw [he]
  exact abs_integral_le_integral_abs

lemma integrable_totalVariation_poisson {n : ℕ} (g : Disorder n)
    (r : ℝ≥0) (x : Spin n) :
    Integrable (fun j => totalVariation ((transition g ^ j) x) (mass g 0))
      (poissonMeasure r) := by
  unfold totalVariation
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro y _
  exact ((integrable_discreteKernel_poisson g r x y).sub (integrable_const _)).abs

lemma poisson_head_integral (r : ℝ≥0) (k : ℕ) :
    (∫ j : ℕ, (if j < k then (1:ℝ) else 0) ∂poissonMeasure r) =
      ∑ j ∈ Finset.range k, Clock.poissonMass r j := by
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
    (g : Disorder n) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    continuousDistance g t ≤ (∑ j ∈ Finset.range k, Clock.poissonMass ((n:ℝ)*t) j) +
      discreteDistance g k := by
  let r : ℝ≥0 := ⟨(n:ℝ)*t,mul_nonneg (Nat.cast_nonneg n) ht⟩
  apply Finset.sup'_le
  intro x _
  change totalVariation (continuousKernel (coupling g) t x) (mass g 0) ≤ _
  have he : continuousKernel (coupling g) t x =
      fun y => ∫ j, (transition g ^ j) x y ∂poissonMeasure r := by
    funext y
    exact continuousKernel_poisson_integral hn g t ht x y
  rw [he]
  apply (totalVariation_integral_le _ _ _ (integrable_discreteKernel_poisson g r x)).trans
  have hbi : Integrable (fun j : ℕ => if j < k then (1:ℝ) else 0) (poissonMeasure r) := by
    apply Integrable.mono' (integrable_const (1:ℝ)) (.of_discrete)
    exact ae_of_all _ (fun j => by split_ifs <;> norm_num)
  calc
    _ ≤ ∫ j : ℕ, (if j < k then (1:ℝ) else 0)+discreteDistance g k ∂poissonMeasure r := by
      apply integral_mono (integrable_totalVariation_poisson g r x)
        (hbi.add (integrable_const _))
      intro j
      change totalVariation ((transition g ^ j) x) (mass g 0) ≤
        (if j < k then (1:ℝ) else 0)+discreteDistance g k
      by_cases hj : j < k
      · simp only [ite_eq_left hj]
        have hb := (tv_le_discreteDistance g j x).trans (discreteDistance_le_one g j)
        linarith [discreteDistance_nonneg g k]
      · simp only [ite_eq_right hj, zero_add]
        exact (tv_le_discreteDistance g j x).trans
          (discreteDistance_antitone g (not_lt.mp hj))
    _ = _ := by
      rw [integral_add hbi (integrable_const _), poisson_head_integral]
      have hu : (poissonMeasure r).real Set.univ = 1 := by
        simp [Measure.real, measure_univ]
      simp only [integral_const, smul_eq_mul, hu, one_mul]
      rfl

lemma uniform_lower_clock_error
    (G : ∀ n : ℕ, Set (Disorder n)) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      (∑ j ∈ Finset.range ⌊(1-b)*(n:ℝ)*medianTime g⌋₊,
        Clock.poissonMass ((n:ℝ)*((1-b/2)*medianTime g)) j) < ε := by
  let a : ℝ := (1-b)/(1-b/2)
  have hmid : 0 < 1-b/2 := by linarith
  have ha1 : a < 1 := by
    apply (div_lt_one hmid).mpr
    linarith
  obtain ⟨s,c,hs,hc,he⟩ := exists_poisson_head_exponent ha1
  intro ε hε
  have hlim : Tendsto (fun z : ℝ => Real.exp (-c*((1-b/2)*z))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul,id_eq] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_id.const_mul_atTop hmid).const_mul_atTop hc)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  filter_upwards [hdiv R] with n hn
  intro g hg
  have ht := (medianTime_mem g).1
  have hr : 0 ≤ (n:ℝ)*((1-b/2)*medianTime g) := by positivity
  have hkr : (⌊(1-b)*(n:ℝ)*medianTime g⌋₊:ℝ) ≤
      a*((n:ℝ)*((1-b/2)*medianTime g)) := by
    apply (Nat.floor_le (mul_nonneg
      (mul_nonneg (by linarith) (Nat.cast_nonneg _)) ht)).trans
    apply le_of_eq
    dsimp [a]
    have hne : 2-b ≠ 0 := by linarith
    field_simp [hne]
  have hhead := poisson_head_le hr hs.le ⌊(1-b)*(n:ℝ)*medianTime g⌋₊
  have hexp : Real.exp (s*(⌊(1-b)*(n:ℝ)*medianTime g⌋₊:ℝ)+
      ((n:ℝ)*((1-b/2)*medianTime g))*(Real.exp (-s)-1)) ≤
        Real.exp (-c*((1-b/2)*((n:ℝ)*medianTime g))) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ s*(a*((n:ℝ)*((1-b/2)*medianTime g)))+
          ((n:ℝ)*((1-b/2)*medianTime g))*(Real.exp (-s)-1) := by
        gcongr
      _ = (s*a+Real.exp (-s)-1)*((n:ℝ)*((1-b/2)*medianTime g)) := by ring
      _ = _ := by rw [he]; ring
  exact (hhead.trans hexp).trans_lt (hR _ (hn g hg))

theorem uniform_discrete_lower_from_continuous
    (G : ∀ n : ℕ, Set (Disorder n)) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g)
    (hcont : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-δ < continuousDistance g ((1-b/2)*medianTime g)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-δ < discreteDistance g ⌊(1-b)*(n:ℝ)*medianTime g⌋₊ := by
  intro δ hδ
  filter_upwards [hcont (δ/2) (by positivity),
    uniform_lower_clock_error G hb hb1 hdiv (δ/2) (by positivity),
    eventually_gt_atTop 0] with n hn he hn0
  intro g hg
  have h := continuous_le_poisson_head_add_discrete hn0 g ((1-b/2)*medianTime g)
    (mul_nonneg (by linarith) (medianTime_mem g).1) ⌊(1-b)*(n:ℝ)*medianTime g⌋₊
  have hc := hn g hg
  have he' := he g hg
  linarith

end SKRatio.Calculus

end
end

end OAI
