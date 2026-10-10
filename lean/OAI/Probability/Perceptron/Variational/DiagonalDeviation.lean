import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma exists_slow_diagonal {b : ℕ→ℕ→ℝ} (hb : ∀ n p, 0≤b n p)
    (hlim : ∀ p, Tendsto (fun n => b n p) atTop (𝓝 0)) :
    ∃ J : ℕ→ℕ, Monotone J ∧ (∀ n, J n≤n) ∧ Tendsto J atTop atTop ∧
      Tendsto (fun n => ∑ p∈Finset.range (J n), b n p) atTop (𝓝 0) := by
  classical
  let P := fun n k => ∀ m≥n, (∑ p∈Finset.range k, b m p)≤1/(k+1:ℝ)
  have hP0 (n) : P n 0 := by intro m hm; simp
  let J := fun n => Nat.findGreatest (P n) n
  have hJ (n) : J n≤n := Nat.findGreatest_le _
  have hJP (n) : P n (J n) := Nat.findGreatest_spec (Nat.zero_le n) (hP0 n)
  have hJmono : Monotone J := by
    intro m n hmn
    exact Nat.findGreatest_mono (fun k hk l hl => hk l (hmn.trans hl)) hmn
  have hPJ (k) : ∀ᶠ n in atTop, k≤J n := by
    have hs : Tendsto (fun n => ∑ p∈Finset.range k, b n p) atTop (𝓝 (0:ℝ)) := by
      simpa using tendsto_finsetSum (Finset.range k) (fun p _ => hlim p)
    have he := hs.eventually (gt_mem_nhds (by positivity : (0:ℝ)<1/(k+1:ℝ)))
    obtain ⟨N,hN⟩ := eventually_atTop.1 he
    filter_upwards [eventually_ge_atTop (max N k)] with n hn
    exact Nat.le_findGreatest ((le_max_right N k).trans hn)
      (fun m hm => (hN m ((le_max_left N k).trans (hn.trans hm))).le)
  have hJlim : Tendsto J atTop atTop := tendsto_atTop.2 hPJ
  refine ⟨J,hJmono,hJ,hJlim,?_⟩
  apply squeeze_zero (fun n => Finset.sum_nonneg (fun p _ => hb n p))
    (fun n => hJP n n le_rfl)
  have hh : Tendsto (fun n => (J n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hJlim).atTop_add tendsto_const_nhds
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hh

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (d : ℕ→ℕ→X→ℝ)

def diagonalDeviationMass (J : ℕ→ℕ) (n : ℕ) : ℝ :=
  ∑ p∈Finset.range (J n), ∫ v, d n p v ∂μ

def diagonalDeviationThreshold (J : ℕ→ℕ) (n : ℕ) : ℝ :=
  Real.sqrt (diagonalDeviationMass μ d J n)+1/(n+1:ℝ)

def diagonalGoodSet (J : ℕ→ℕ) (n : ℕ) : Set X :=
  {v | ∀ p∈Finset.range (J n), d n p v≤diagonalDeviationThreshold μ d J n}

lemma diagonalDeviationThreshold_pos (J : ℕ→ℕ) (n : ℕ) :
    0<diagonalDeviationThreshold μ d J n := by
  unfold diagonalDeviationThreshold
  exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity)

lemma diagonalGoodSet_measurable (hm : ∀ n p, Measurable (d n p)) (J : ℕ→ℕ) (n : ℕ) :
    MeasurableSet (diagonalGoodSet μ d J n) := by
  unfold diagonalGoodSet
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_le (hm n p) measurable_const

lemma diagonalGoodSet_compl_bound [IsProbabilityMeasure μ] (hn : ∀ n p v, 0≤d n p v)
    (hi : ∀ n p, Integrable (d n p) μ) (J : ℕ→ℕ) (n : ℕ) :
    μ.real (diagonalGoodSet μ d J n)ᶜ ≤ Real.sqrt (diagonalDeviationMass μ d J n) := by
  let S := fun v => ∑ p∈Finset.range (J n), d n p v
  have hSn (v) : 0≤S v := Finset.sum_nonneg fun p _ => hn n p v
  have hSi : Integrable S μ := integrable_finsetSum _ (fun p _ => hi n p)
  have hSm : ∫ v, S v ∂μ = diagonalDeviationMass μ d J n := integral_finsetSum _ (fun p _ => hi n p)
  have ha : 0≤diagonalDeviationMass μ d J n := hSm ▸ integral_nonneg hSn
  have hs : (diagonalGoodSet μ d J n)ᶜ ⊆ {v | diagonalDeviationThreshold μ d J n≤S v} := by
    intro v hv
    simp only [diagonalGoodSet,mem_compl_iff,mem_ofPred_eq,not_forall,not_le] at hv
    obtain ⟨p,hp,hpv⟩ := hv
    exact hpv.le.trans (Finset.single_le_sum (fun q _ => hn n q v) hp)
  have hb := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hSn) hSi
    (diagonalDeviationThreshold μ d J n)
  rw [hSm] at hb
  have he := diagonalDeviationThreshold_pos μ d J n
  calc
    _ ≤ μ.real {v | diagonalDeviationThreshold μ d J n≤S v} := measureReal_mono hs
    _ ≤ diagonalDeviationMass μ d J n/diagonalDeviationThreshold μ d J n :=
      (le_div_iff₀ he).2 (by simpa [mul_comm] using hb)
    _ ≤ Real.sqrt (diagonalDeviationMass μ d J n) := by
      apply (div_le_iff₀ he).2
      dsimp [diagonalDeviationThreshold]
      nlinarith [Real.sq_sqrt ha, mul_nonneg (Real.sqrt_nonneg (diagonalDeviationMass μ d J n))
        (by positivity : (0:ℝ)≤1/(n+1:ℝ))]

lemma diagonalGoodSet_compl_tendsto [IsProbabilityMeasure μ] (hn : ∀ n p v, 0≤d n p v)
    (hi : ∀ n p, Integrable (d n p) μ) (J : ℕ→ℕ)
    (hJ : Tendsto (diagonalDeviationMass μ d J) atTop (𝓝 0)) :
    Tendsto (fun n => μ.real (diagonalGoodSet μ d J n)ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => measureReal_nonneg)
    (diagonalGoodSet_compl_bound μ d hn hi J)
  simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hJ

lemma diagonalDeviationThreshold_tendsto (J : ℕ→ℕ)
    (hJ : Tendsto (diagonalDeviationMass μ d J) atTop (𝓝 0)) :
    Tendsto (diagonalDeviationThreshold μ d J) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  change Tendsto (fun n => Real.sqrt (diagonalDeviationMass μ d J n)+1/(n+1:ℝ)) atTop (𝓝 0)
  simpa only [Function.comp_def,Real.sqrt_zero,zero_add] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hJ).add h1

lemma diagonalGoodSet_deviation_tendsto (hn : ∀ n p v, 0≤d n p v) (J : ℕ→ℕ)
    (hJ : Tendsto J atTop atTop) (hmass : Tendsto (diagonalDeviationMass μ d J) atTop (𝓝 0))
    (v : ℕ→X) (hv : ∀ᶠ n in atTop, v n∈diagonalGoodSet μ d J n) (p : ℕ) :
    Tendsto (fun n => d n p (v n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => hn n p (v n)) _
    (diagonalDeviationThreshold_tendsto μ d J hmass)
  filter_upwards [hv, hJ.eventually (eventually_gt_atTop p)] with n hn hnp
  exact hn p (Finset.mem_range.2 hnp)

end SphericalPerceptronFreeEnergy
end

end OAI
