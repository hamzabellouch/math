import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFChainAverage
import OAI.Probability.SKBarriers.Scalar.ScalarSplit
import OAI.Probability.SKBarriers.Parisi.CDFOverlap
import OAI.Probability.SKBarriers.Scalar.DyadicVaryingTerminal
import OAI.Probability.SKBarriers.Scalar.DyadicPenalty

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarTimeChainAverage_spin_gradient (β : ℝ) (l : List (ℝ × ℝ≥0)) :
    scalarTimeChainAverage β l scalarSpinTerminal scalarMagnetization=
      rootGradient 0 (scalarTimeChain β l scalarSpinTerminal) := by
  funext x
  rw [← (scalarTimeChain_spin_hasDerivAt β l x).deriv,scalarTimeChain_eq_hierarchy]
  exact (scalarHierarchy_gradient_average _ _ _ scalarSpinTerminal_regular scalarSpinTerminal_hasDerivAt x).symm

theorem dyadicScalar_varying_terminal_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hF : ∀ n, BoundedDerivs (F n))
    (hf : BoundedDerivs f) {K : ℝ≥0} (hfK : LipschitzWith K f)
    (hFf : TendstoUniformly F f atTop) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => dyadicScalar β α n s t (F n))
      (scalarCDFOperator β α s t f) atTop := by
  have H := dyadicScalar_general_uniform hf hfK β hα hmono s t ht
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hFf (ε/2) (half_pos hε),
    Metric.tendstoUniformly_iff.mp H (ε/2) (half_pos hε)] with n hfn hn x
  have H' := dyadicScalar_uniform_nonexpansive (hF n) hf β hα n s t
    (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hfn z).le) x
  rw [Real.dist_eq,abs_sub_comm]
  calc
    _ ≤ |dyadicScalar β α n s t (F n) x-dyadicScalar β α n s t f x|+
        |dyadicScalar β α n s t f x-scalarCDFOperator β α s t f x| := abs_sub_le _ _ _
    _ < ε/2+ε/2 := add_lt_add_of_le_of_lt H' (by simpa only [Real.dist_eq,abs_sub_comm] using hn x)
    _ = ε := add_halves ε

theorem dyadicPenalty_tendsto {α : ℝ → ℝ} (hα : Monotone α)
    (s : ℝ) (t : ℝ≥0) (hs : 0 ≤ s) (ht : s+t ≤ 1) :
    Tendsto (fun n => chainQuadraticPenalty s (dyadicIntervals α n s t)) atTop
      (𝓝 (2*∫ u in s..s+t, u*α u)) := by
  have H : Tendsto (fun n : ℕ => 2*(t:ℝ)/(2:ℝ)^n*(α (s+t)-α s)) atTop (𝓝 0) := by
    have Hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul (2*(t:ℝ)*(α (s+t)-α s))
    convert Hp using 1
    · funext n
      rw [div_pow,one_pow]
      ring
    · ring_nf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp H).2 ε hε] with n hn
  rw [Real.dist_eq]
  exact (dyadicPenalty_error hα n s t hs ht).trans_lt hn

theorem dyadicPairOverlap_tendsto (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    Tendsto (fun n => scalarTimeChainAverage β (dyadicIntervals α n 0 (Real.toNNReal q))
      (scalarTimeChain β (dyadicIntervals α n q (Real.toNNReal (1-q))) scalarSpinTerminal)
      (fun x => (scalarTimeChainAverage β (dyadicIntervals α n q (Real.toNNReal (1-q)))
        scalarSpinTerminal scalarMagnetization x)^2) 0) atTop (𝓝 (scalarCDFOverlap β α q)) := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : t ≤ 1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hq.1,NNReal.coe_one]; exact hq.2
  have hr : r ≤ 1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (sub_nonneg.mpr hq.2),NNReal.coe_one]; linarith [hq.1]
  let F (n : ℕ) := dyadicScalar β α n q r scalarSpinTerminal
  let A (n : ℕ) := fun x => (rootGradient 0 (F n) x)^2
  have hsq := scalarCDFGradient_sq_regular β ha hm q r hr
  have hAu : TendstoUniformly A (fun x => (scalarCDFGradient β α q r x)^2) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp (dyadicScalar_gradient_uniform β ha hm q r hr)
      (ε/2) (half_pos hε)] with n hn x
    rw [Real.dist_eq,abs_sub_comm]
    have H := abs_sq_sub_sq_le_two (dyadicScalar_spin_bounds β ha n q r x).1
      (scalarCDF_derivative_bounds β ha hm q r hr x).1
    have H' : |rootGradient 0 (F n) x-scalarCDFGradient β α q r x|<ε/2 := by
      simpa only [Real.dist_eq,abs_sub_comm] using hn x
    exact H.trans_lt (by nlinarith)
  have H := dyadicScalarAverage_varying_terminal β ha hm
    (fun n => dyadicScalar_regular scalarSpinTerminal_regular β α n q r)
    (scalarCDFValue_regular β ha hm q r hr)
    (show ∀ n, Continuous (A n) from fun n =>
      (scalarTimeChain_spin_gradient_lipschitz β _
        (fun _ hp => dyadicIntervals_mass_bounds ha n q r hp)).continuous.pow 2)
    hsq.1 hsq.2.1 (scalarCDFValue_lipschitz β ha hm q r hr)
    (B:=1) (C:=2)
    (fun n x => by
      change |(rootGradient 0 (F n) x)^2| ≤ (1:ℝ)
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (dyadicScalar_spin_bounds β ha n q r x).1)
    hsq.2.2.1 hsq.2.2.2 (dyadicScalar_value_uniform β ha hm q r hr) hAu 0 t ht 0
  simp_rw [scalarTimeChainAverage_spin_gradient]
  change Tendsto (fun n => dyadicScalarAverage β α n 0 t (F n) (A n) 0)
    atTop (𝓝 (scalarCDFOverlap β α q))
  exact H

end SK.Analytic

end
end

end OAI
