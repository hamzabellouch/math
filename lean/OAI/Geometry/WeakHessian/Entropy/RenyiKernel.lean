import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SubConst
import OAI.Geometry.WeakHessian.Sobolev.AddConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open scoped Topology

namespace WeakHessian

def renyiKernel (a r : ℝ) : ℝ := (r-r^(1-a))/a+1-r

lemma renyiKernel_nonneg {a r : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 ≤ r) :
    0 ≤ renyiKernel a r := by
  have H := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ 1-a by linarith) ha.le hr (show (0:ℝ) ≤ 1 by norm_num) (by ring : 1-a+a=1)
  simp only [Real.one_rpow,mul_one] at H
  have H' : (r-1)*a ≤ r-r^(1-a) := by nlinarith
  have H'' := (le_div_iff₀ ha).mpr H'
  unfold renyiKernel
  linarith

lemma rpow_sub_le_add_one {a r : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r) :
    r^(1-a) ≤ r+1 := by
  have H := Real.geom_mean_le_arith_mean2_weighted (show 0 ≤ 1-a by linarith)
    ha hr (show (0:ℝ) ≤ 1 by norm_num) (by ring : 1-a+a=1)
  simp only [Real.one_rpow,mul_one] at H
  nlinarith [mul_nonneg ha hr]

lemma tendsto_renyiKernel {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun a => renyiKernel a r) (𝓝[>] 0) (𝓝 (klFun r)) := by
  rcases hr.eq_or_lt with rfl | hr
  · have ha : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [ha] with a ha
    simp [renyiKernel,klFun,Real.zero_rpow (by linarith : (1-a:ℝ) ≠ 0)]
  · have hd : HasDerivAt (fun a : ℝ => r^(1-a)) (-r*Real.log r) 0 := by
      convert HasDerivAt.const_rpow hr ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id 0)) using 1
      <;> first | rfl | (simp; ring)
    have H := hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0:ℝ))
    have H' := (H.neg.add_const 1).sub_const r
    convert H' using 1
    · ext a
      simp only [renyiKernel,slope_def_field,sub_zero,Real.rpow_one]
      ring
    · simp only [klFun]
      congr 1
      ring

lemma continuous_renyiKernel (a : ℝ) (ha : a < 1) : Continuous (renyiKernel a) := by
  unfold renyiKernel
  fun_prop (disch := linarith)

lemma renyiKernel_large_dimension {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => renyiKernel (1/((n:ℝ)+2)) r) atTop (𝓝 (klFun r)) := by
  have hlim : Tendsto (fun n : ℕ => 1/((n:ℝ)+2)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 2).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  apply (tendsto_renyiKernel hr).comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall (fun n => by change 0 < 1/((n:ℝ)+2); positivity)⟩

open InformationTheory

variable {X : Type*} [MeasurableSpace X]

lemma renyiKernel_le_klFun {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 0 ≤ r) :
    renyiKernel a r ≤ klFun r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [renyiKernel, klFun, Real.zero_rpow (by linarith : (1-a:ℝ) ≠ 0)]
  have H := Real.add_one_le_exp (-a*Real.log r)
  have hp : r^(1-a) = r*Real.exp (-a*Real.log r) := by
    rw [Real.rpow_def_of_pos hr]
    rw [show Real.log r * (1-a) = Real.log r + (-a*Real.log r) by ring,
      Real.exp_add,Real.exp_log hr]
  have HH : (r-r^(1-a))/a ≤ r*Real.log r := by
    apply (div_le_iff₀ ha).mpr
    rw [hp]
    nlinarith [mul_le_mul_of_nonneg_left H hr.le]
  unfold renyiKernel klFun
  linarith

lemma integrable_rpow_sub {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Integrable (fun x => (r x)^(1-a)) m := by
  apply (hr.add (integrable_const 1)).mono'
  · exact (Real.continuous_rpow_const (by linarith : 0 ≤ 1-a)).comp_aestronglyMeasurable hr.1
  · filter_upwards [hr0] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx _)]
    exact rpow_sub_le_add_one ha ha1.le hx

lemma integrable_renyiKernel {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Integrable (fun x => renyiKernel a (r x)) m := by
  exact (((hr.sub (integrable_rpow_sub hr hr0 ha ha1)).div_const a).add (integrable_const 1)).sub hr

lemma tendsto_integral_rpow_sub {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n < 1) (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (r x)^(1-a n) ∂m) atTop (𝓝 (∫ x, r x ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => r x+1)
  · exact fun n => (integrable_rpow_sub hr hr0 (ha n) (ha1 n)).1
  · exact hr.add (integrable_const 1)
  · intro n
    filter_upwards [hr0] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx _)]
    exact rpow_sub_le_add_one (ha n) (ha1 n).le hx
  · filter_upwards [hr0] with x hx
    simpa only [sub_zero, Real.rpow_one, Function.comp_def] using
      (Real.continuousAt_rpow (r x,1) (Or.inr zero_lt_one)).tendsto.comp
        (tendsto_const_nhds.prodMk_nhds (by simpa using (tendsto_const_nhds.sub halim : Tendsto (fun n => (1:ℝ)-a n) atTop (𝓝 (1-0)))))

lemma integral_klFun_le_of_renyi_bounds {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x) {a B : ℕ → ℝ} {L : ℝ}
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1) (halim : Tendsto a atTop (𝓝 0))
    (hb : ∀ n, ∫ x, renyiKernel (a n) (r x) ∂m ≤ B n) (hB : Tendsto B atTop (𝓝 L)) :
    Integrable (fun x => klFun (r x)) m ∧ (∫ x, klFun (r x) ∂m) ≤ L := by
  have hmeas : AEStronglyMeasurable (fun x => klFun (r x)) m :=
    continuous_klFun.comp_aestronglyMeasurable hr.1
  have hn : ∀ n, 0 ≤ᵐ[m] fun x => renyiKernel (a n) (r x) :=
    fun n => hr0.mono (fun x hx => renyiKernel_nonneg (ha n) (ha1 n).le hx)
  have hni := fun n => integrable_renyiKernel hr hr0 (ha n).le (ha1 n)
  have hlim : ∀ᵐ x ∂m, Tendsto (fun n => ENNReal.ofReal (renyiKernel (a n) (r x)))
      atTop (𝓝 (ENNReal.ofReal (klFun (r x)))) := by
    filter_upwards [hr0] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_renyiKernel hx).comp
      (tendsto_nhdsWithin_iff.mpr ⟨halim,Eventually.of_forall ha⟩))
  have hfat : (∫⁻ x, ENNReal.ofReal (klFun (r x)) ∂m) ≤ ENNReal.ofReal L := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (renyiKernel (a n) (r x))) atTop ∂m :=
        lintegral_congr_ae (hlim.mono (fun x hx => hx.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (renyiKernel (a n) (r x)) ∂m) atTop :=
        lintegral_liminf_le' (fun n => (hni n).1.aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun n => ENNReal.ofReal (B n)) atTop := by
        simp only [liminf_eq_iSup_iInf_of_nat]
        apply iSup_mono
        intro k
        apply iInf_mono
        intro n
        apply iInf_mono
        intro hkn
        rw [← ofReal_integral_eq_lintegral_ofReal (hni n) (hn n)]
        exact ENNReal.ofReal_le_ofReal (hb n)
      _ = _ := ((ENNReal.continuous_ofReal.tendsto _).comp hB).liminf_eq
  have hint : Integrable (fun x => klFun (r x)) m :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas (hr0.mono fun x hx => klFun_nonneg hx)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfat)
  have hL : 0 ≤ L := ge_of_tendsto hB (Eventually.of_forall fun n =>
    (integral_nonneg_of_ae (hn n)).trans (hb n))
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (hr0.mono fun x hx => klFun_nonneg hx)] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hL).mp hfat

lemma tendsto_integral_renyiKernel {m : Measure X} [IsFiniteMeasure m] {r : X → ℝ}
    (hr : Integrable r m) (hr0 : ∀ᵐ x ∂m, 0 ≤ r x)
    (hkl : Integrable (fun x => klFun (r x)) m) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1) (halim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, renyiKernel (a n) (r x) ∂m) atTop
      (𝓝 (∫ x, klFun (r x) ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => klFun (r x))
  · exact fun n => (integrable_renyiKernel hr hr0 (ha n).le (ha1 n)).1
  · exact hkl
  · intro n
    filter_upwards [hr0] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (renyiKernel_nonneg (ha n) (ha1 n).le hx)]
    exact renyiKernel_le_klFun (ha n) (ha1 n) hx
  · exact hr0.mono (fun x hx => (tendsto_renyiKernel hx).comp
      (tendsto_nhdsWithin_iff.mpr ⟨halim,Eventually.of_forall ha⟩))
end WeakHessian

end

end OAI
