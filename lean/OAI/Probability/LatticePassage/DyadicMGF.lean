import OAI.Probability.LatticePassage.PassageMGF
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Filter Topology

theorem dyadic_derivative_bound (G : ℝ → ℝ) (a m K : ℝ) (hK : 0 ≤ K)
    (hzero : G 0 = 0) (hd : HasDerivAt G m 0)
    (hrec : ∀ n : ℕ, G (a*(1/2 : ℝ)^n) ≤
      2*G (a*(1/2 : ℝ)^(n+1)) + K*((1/2 : ℝ)^n)^2) :
    G a ≤ a*m+2*K := by
  have hi : ∀ n : ℕ, G a ≤ G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n +
      2*K*(1-(1/2 : ℝ)^n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) n
      have hdiv := div_le_div_of_nonneg_right (hrec n) hn.le
      calc
        _ ≤ G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n + 2*K*(1-(1/2 : ℝ)^n) := ih
        _ ≤ (2*G (a*(1/2 : ℝ)^(n+1))+K*((1/2 : ℝ)^n)^2)/(1/2 : ℝ)^n +
            2*K*(1-(1/2 : ℝ)^n) := add_le_add hdiv le_rfl
        _ = _ := by
          rw [pow_succ]
          field_simp
          ring
  by_cases ha : a = 0
  · subst a
    simp only [hzero, zero_mul, zero_add]
    positivity
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun n : ℕ => a*(1/2 : ℝ)^n) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hp.const_mul a
    · exact .of_forall (fun n => by simp [ha])
  have hsl := (hd.tendsto_slope.comp hb).const_mul a
  have hmain : Tendsto (fun n : ℕ => G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n)
      atTop (𝓝 (a*m)) := by
    convert hsl using 1
    funext n
    simp only [Function.comp_def, slope, sub_zero, hzero, smul_eq_mul, vsub_eq_sub, sub_zero]
    field_simp [ha]
  have hc : Tendsto (fun n : ℕ => 2*K*(1-(1/2 : ℝ)^n)) atTop (𝓝 (2*K)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul (2*K)
  exact ge_of_tendsto (hmain.add hc) (.of_forall hi)

theorem finitePassageTime_cgf_centered (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2)
    (hq : 4*a^2*R ≤ 1/2) :
    cgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a ≤
      a*(∫ v, finitePassageTime x y R v
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) + 16*a^2*R := by
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet F P) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
    intro t ht
    exact integrable_finitePassageTime_exp x y R hR t ht.le
  have hd : HasDerivAt (cgf F P) (∫ v, F v ∂P) 0 := by
    have h := (analyticAt_cgf h0).differentiableAt.hasDerivAt
    rw [deriv_cgf_zero h0] at h
    simpa using h
  have hb := dyadic_derivative_bound (cgf F P) a (∫ v, F v ∂P) (8*a^2*R)
    (by positivity) (cgf_zero (X := F) (μ := P)) hd (fun n => ?_)
  · convert hb using 1; ring
  have hn0 : 0 ≤ (1/2 : ℝ)^n := by positivity
  have hn1 : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have han : |a*(1/2 : ℝ)^n| ≤ 1/2 := by
    rw [abs_mul, abs_of_nonneg hn0]
    calc
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left hn1 (abs_nonneg a)
      _ ≤ _ := by simpa using ha
  have hqn : 4*(a*(1/2 : ℝ)^n)^2*R ≤ 1/2 := by
    have hs : ((1/2 : ℝ)^n)^2 ≤ 1 := by nlinarith
    calc
      _ = (4*a^2*R)*((1/2 : ℝ)^n)^2 := by ring
      _ ≤ (4*a^2*R)*1 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ _ := by simpa using hq
  have hr := finitePassageTime_cgf_recursion x y R hR (a*(1/2 : ℝ)^n) han hqn
  have he : a*(1/2 : ℝ)^n/2 = a*(1/2 : ℝ)^(n+1) := by rw [pow_succ]; ring
  rw [he] at hr
  convert hr using 1; ring

end CompanionFPP

end OAI
