import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.Aggregate

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma hasSum_poisson_pow (r : ℝ≥0) (c : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-(r:ℝ))*(r:ℝ)^n/(n.factorial:ℝ))*c^n)
      (Real.exp ((r:ℝ)*(c-1))) := by
  convert! (NormedSpace.expSeries_div_hasSum_exp ((r:ℝ)*c)).mul_left
    (Real.exp (-(r:ℝ))) using 1
  · ext n
    rw [mul_pow]
    ring
  · rw [←Real.exp_eq_exp_ℝ,←Real.exp_add]
    congr 1
    ring

lemma integrable_poisson_pow (r : ℝ≥0) (c : ℝ) (hc : 0≤c) :
    Integrable (fun n : ℕ => c^n) (poissonMeasure r) := by
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hc _)] using
    (hasSum_poisson_pow r c).summable

lemma integral_poisson_pow (r : ℝ≥0) (c : ℝ) :
    (∫ n : ℕ,c^n ∂poissonMeasure r)=Real.exp ((r:ℝ)*(c-1)) := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (hasSum_poisson_pow r c).tsum_eq

theorem poisson_double_tail (r : ℝ≥0) :
    (poissonMeasure r).real {n : ℕ | 2*(r:ℝ)≤n}≤Real.exp (-(r:ℝ)/4) := by
  let t := Real.exp (2*(r:ℝ)*Real.log 2)
  have ht : 0<t := Real.exp_pos _
  have hsub : {n : ℕ | 2*(r:ℝ)≤n} ⊆ {n : ℕ | t≤(2:ℝ)^n} := by
    intro n hn
    change Real.exp (2*(r:ℝ)*Real.log 2)≤(2:ℝ)^n
    rw [show (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn (Real.log_nonneg (by norm_num)))
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ:=poissonMeasure r) (f:=fun n : ℕ => (2:ℝ)^n)
    (Filter.Eventually.of_forall fun n => by positivity)
    (integrable_poisson_pow r 2 (by norm_num)) t
  rw [integral_poisson_pow] at h
  have he : (poissonMeasure r).real {n : ℕ | t≤(2:ℝ)^n}≤Real.exp (r:ℝ)/t := by
    apply (le_div_iff₀ ht).mpr
    simpa only [sub_self,show (2:ℝ)-1=1 by norm_num,mul_one,mul_comm t] using h
  calc
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ Real.exp (r:ℝ)/t := he
    _ = Real.exp ((r:ℝ)*(1-2*Real.log 2)) := by
      dsimp [t]
      rw [←Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Real.log_two_gt_d9,r.coe_nonneg])

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def sampleCount {R : ℕ} (ω : Fin R→ι→ℕ) : ℕ := ∑r,∑i,ω r i

lemma hasLaw_sampleCount (rate : ι→ℝ≥0) (R : ℕ) :
    HasLaw (sampleCount (R:=R)) (poissonMeasure ((R:ℝ≥0)*∑i,rate i))
      (scheduleMeasure rate R) := by
  have hf := hasLaw_sum (fun p : Fin R×ι => rate p.2) Finset.univ
  have hh := hf.comp (measurePreserving_uncurry_schedule rate R).hasLaw
  convert! hh using 1
  · funext ω
    simp [sampleCount,Fintype.sum_prod_type]
  · congr 1
    simp [Fintype.sum_prod_type]

theorem sampleCount_double_tail (rate : ι→ℝ≥0) (R : ℕ) :
    (scheduleMeasure rate R).real
      {ω | 2*((R:ℝ)*∑i,(rate i:ℝ))≤(sampleCount ω:ℝ)}≤
        Real.exp (-((R:ℝ)*∑i,(rate i:ℝ))/4) := by
  have hh := (hasLaw_sampleCount rate R).measureReal_eq
    (p:=fun n : ℕ => 2*(((R:ℝ≥0)*∑i,rate i):ℝ)≤(n:ℝ)) (by measurability)
  simpa only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_sum] using
    hh.trans_le (poisson_double_tail ((R:ℝ≥0)*∑i,rate i))

end SharpRamseyFive.PoissonScore

end OAI
