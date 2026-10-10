import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOverlap
import OAI.Probability.SKBarriers.Scalar.ScalarSpatialAverage
import OAI.Probability.SKBarriers.Gaussian.LipschitzTerminalStability
import OAI.Probability.SKBarriers.Gaussian.LipschitzCDFStability

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_tendstoUniformly_cdf_lipschitz (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFAverage β (αn n) s t f g)
      (scalarCDFAverage β α s t f g) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let A : ℝ := 2*((L:ℝ)+2*(B:ℝ)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  let h : ℝ := ε/(4*(A+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : A*h<ε := by
    have HE : 4*(A+1)*h=ε := by dsimp [h]; field_simp
    nlinarith
  have HT : Tendsto (fun n =>
      2*(scalarTimeMassConstantK β (K+B+B)*cdfDistance (αn n) α)/h+A*h) atTop (𝓝 (A*h)) := by
    simpa only [mul_zero,zero_div,zero_add] using
      (((hD.const_mul (scalarTimeMassConstantK β (K+B+B))).const_mul 2).div_const h).add_const (A*h)
  filter_upwards [(tendsto_order.mp HT).2 ε hsmall] with n hbound x
  rw [Real.dist_eq,abs_sub_comm]
  have H := scalarCDFAverage_cdf_stability_lipschitz β (hn n) (hnm n) hα hαm
    hf hfK hgL hB s t ht x h hh
  have HD := cdfDistance_subinterval_le (hnm n) hαm hs hst
  apply (H.trans ?_).trans_lt hbound
  exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HD (scalarTimeMassConstantK_nonneg β _)) (by norm_num : (0:ℝ)≤2)) hh.le) le_rfl

theorem scalarCDFAverage_abs_le (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f g x|≤B := by
  apply le_of_tendsto (dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht x).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_abs_le hf hB _ _ _ _)

theorem scalarCDFAverage_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) :
    LipschitzWith (L+2*B*Real.toNNReal (Real.exp (2*(K:ℝ)))) (scalarCDFAverage β α s t f g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hm hf hfK hgL hB s t ht y)).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_spatial_bound _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _)) (fun i j hij => ?_)
    hf hfK hgL hB x y
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact List.pairwise_iff_get.mp (dyadicIntervals_pairwise hm n s t) i j hij
  · exact le_rfl

theorem scalarCDFAverage_tendstoUniformly_varying (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hn : ∀ n z,αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} {fn gn : ℕ → ℝ → ℝ}
    (hf : BoundedDerivs f) (hfn : ∀ n,BoundedDerivs (fn n)) {K L B : ℝ≥0}
    (hfK : LipschitzWith K f) (hfnK : ∀ n,LipschitzWith K (fn n))
    (hgL : LipschitzWith L g) (hgnL : ∀ n,LipschitzWith L (gn n))
    (hgB : ∀ z,|g z|≤B) (hgnB : ∀ n z,|gn n z|≤B)
    (hfU : TendstoUniformly fn f atTop) (hgU : TendstoUniformly gn g atTop)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFAverage β (αn n) s t (fn n) (gn n))
      (scalarCDFAverage β α s t f g) atTop := by
  have hfix := scalarCDFAverage_tendstoUniformly_cdf_lipschitz β hα hm hn hnm hD hf hfK hgL hgB s t ht hs hst
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let φ : ℝ → ℝ := fun e => 2*e+2*(B:ℝ)*(Real.exp (2*e)-1)
  have hφ : ContinuousAt φ 0 := by dsimp [φ]; fun_prop
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp hφ ε hε
  let e := δ/2
  have he : 0<e := half_pos hδ
  have hsmall : φ e<ε := by
    have H := hbound (show dist e 0<δ by rw [Real.dist_eq,sub_zero,abs_of_pos he]; dsimp [e]; linarith)
    have hz : φ 0=0 := by simp [φ]
    rw [hz,Real.dist_eq,sub_zero] at H
    exact (le_abs_self _).trans_lt H
  filter_upwards [Metric.tendstoUniformly_iff.mp hfU e he,
    Metric.tendstoUniformly_iff.mp hgU e he,Metric.tendstoUniformly_iff.mp hfix e he] with n hfn' hgn' hfix' x
  have H := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n) (hfn n) hf
    (hfnK n) hfK (hgnL n) hgL (hgnB n) hgB he.le
    (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hfn' z).le)
    (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hgn' z).le) s t ht x
  have hf' := hfix' x
  rw [Real.dist_eq,abs_sub_comm] at hf' ⊢
  have HT := abs_sub_le (scalarCDFAverage β (αn n) s t (fn n) (gn n) x)
    (scalarCDFAverage β (αn n) s t f g x) (scalarCDFAverage β α s t f g x)
  have HA : |scalarCDFAverage β (αn n) s t (fn n) (gn n) x-scalarCDFAverage β α s t f g x|<φ e := by
    dsimp [φ]
    linarith
  exact HA.trans hsmall

end SK.Analytic

end
end

end OAI
