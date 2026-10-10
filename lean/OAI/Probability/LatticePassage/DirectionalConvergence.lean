import OAI.Probability.LatticePassage.MetricConcentration
import OAI.Probability.LatticePassage.MeanPositivity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology

lemma exp_neg_sqrt_le (a m : ℝ) (ha : 0 < a) (hm : 0 < m) :
    exp (-(a*sqrt m)) ≤ (24/a^4)/m^2 := by
  have h := Real.pow_div_factorial_le_exp (a*sqrt m) (by positivity) 4
  have hs := sq_sqrt hm.le
  have he : (a*sqrt m)^4 = a^4*m^2 := by
    rw [mul_pow, show sqrt m^4 = (sqrt m^2)^2 by ring, hs]
  rw [he] at h
  norm_num at h
  rw [exp_neg, ← one_div, div_div]
  apply (div_le_div_iff₀ (exp_pos _) (by positivity)).mpr
  nlinarith

lemma summable_exp_neg_sqrt (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => exp (-(a*sqrt (n+1)))) := by
  have h := ((summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
    (show Function.Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h)).mul_left (24/a^4)
  apply h.of_nonneg_of_le (fun n => (exp_pos _).le)
  intro n
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_one_div] using exp_neg_sqrt_le a (n+1) ha (by positivity)

lemma directional_centered_tail (x : Vertex) (hx : x ≠ 0) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    environmentLaw.real {ω | ε*(n+1) ≤
      |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)|} ≤
      ((2*exp 1+4)*exp 10)*exp (-((ε/(64*sqrt (latticeDistance 0 x)))*sqrt (n+1))) := by
  have hd : 0 < latticeDistance 0 x := by
    by_contra h
    have hz : latticeDistance 0 x = 0 := by omega
    apply hx
    ext <;> simp_all [latticeDistance]
  have hd' : (0 : ℝ) < latticeDistance 0 x := by exact_mod_cast hd
  have hm : 1 ≤ latticeDistance 0 (scaleVertex (n+1) x) := by
    rw [latticeDistance_scaleVertex]
    nlinarith
  have ht := passageTime_centered_concentration 0 (scaleVertex (n+1) x) hm
    ((ε/sqrt (latticeDistance 0 x))*sqrt (n+1)) (by positivity)
  rw [latticeDistance_scaleVertex, Nat.cast_mul, Nat.cast_add, Nat.cast_one, sqrt_mul (by positivity)] at ht
  have he : ε/sqrt (latticeDistance 0 x)*sqrt (n+1)*
      (sqrt (n+1)*sqrt (latticeDistance 0 x)) = ε*(n+1) := by
    have hs : sqrt (latticeDistance 0 x) ≠ 0 := (sqrt_pos.mpr hd').ne'
    have hn := sq_sqrt (show (0 : ℝ) ≤ n+1 by positivity)
    field_simp
    nlinarith
  rw [he] at ht
  convert ht using 1 <;> try rfl
  congr 2
  ring

lemma ae_directional_centered_small (x : Vertex) (hx : x ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂environmentLaw, ∀ᶠ n : ℕ in atTop,
      |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)| < ε*(n+1) := by
  have hd : (0 : ℝ) < latticeDistance 0 x := by
    have h : 0 < latticeDistance 0 x := by
      by_contra h
      have hz : latticeDistance 0 x = 0 := by omega
      apply hx
      ext <;> simp_all [latticeDistance]
    exact_mod_cast h
  have hs := (summable_exp_neg_sqrt (ε/(64*sqrt (latticeDistance 0 x))) (by positivity)).mul_left
    ((2*exp 1+4)*exp 10)
  have hsum : Summable (fun n : ℕ => environmentLaw.real {ω |
      ε*(n+1) ≤ |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)|}) :=
    hs.of_nonneg_of_le (fun _ => measureReal_nonneg) (directional_centered_tail x hx ε hε)
  have hsum' : (∑' n : ℕ, environmentLaw {ω |
      ε*(n+1) ≤ |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)|}) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top
  simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hsum'

theorem passageTime_directional_tendsto (x : Vertex) :
    ∀ᵐ ω ∂environmentLaw,
      Tendsto (fun n : ℕ => passageTime ω 0 (scaleVertex n x)/(n : ℝ)) atTop
        (𝓝 (directionalMeanConstant x)) := by
  by_cases hx : x = 0
  · subst x
    have hm : directionalMeanConstant 0 = 0 := by
      apply le_antisymm _ (directionalMeanConstant_nonneg 0)
      apply (directionalMeanConstant_le_mean 0).trans_eq
      apply integral_eq_zero_of_ae
      filter_upwards [passageTime_properties] with ω hω
      exact hω.2.1 0
    filter_upwards [passageTime_properties] with ω hω
    have hz : ∀ n, scaleVertex n (0 : Vertex) = 0 := by intro n; ext <;> simp [scaleVertex]
    simp_rw [hz, hω.2.1 0, zero_div, hm]
    exact tendsto_const_nhds
  · have hall : ∀ᵐ ω ∂environmentLaw, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
        |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)| <
          (1/(k+1 : ℝ))*(n+1) :=
      ae_all_iff.mpr (fun k => ae_directional_centered_small x hx (1/(k+1)) (by positivity))
    filter_upwards [hall] with ω hω
    have hz : Tendsto (fun n : ℕ =>
        (passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1))/(n+1 : ℝ))
        atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
      filter_upwards [hω k] with n hn
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n+1)]
      exact ((div_lt_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr hn).trans hk
    have hm := (meanPassageSequence_tendsto x).comp (tendsto_add_atTop_nat 1)
    have ht := hz.add hm
    have hs : Tendsto (fun n : ℕ => passageTime ω 0 (scaleVertex (n+1) x)/(n+1 : ℝ))
        atTop (𝓝 (directionalMeanConstant x)) := by
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, sub_div, sub_add_cancel, zero_add] using ht
    exact (tendsto_add_atTop_iff_nat 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using hs)

theorem passageTime_all_directions_tendsto :
    ∀ᵐ ω ∂environmentLaw, ∀ x : Vertex,
      Tendsto (fun n : ℕ => passageTime ω 0 (scaleVertex n x)/(n : ℝ)) atTop
        (𝓝 (directionalMeanConstant x)) :=
  ae_all_iff.mpr passageTime_directional_tendsto

end CompanionFPP

end OAI
