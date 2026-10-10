import Mathlib
import OAI.Probability.SKBarriers.Gaussian.LipschitzTerminalStability
import OAI.Probability.SKBarriers.Parisi.CDFIntervalConvergence

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem unitBoundedSquare_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∀ x,|f x|≤1) :
    LipschitzWith (2*K) (fun x => (f x)^2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_mul,NNReal.coe_ofNat]
  have H := (abs_sq_sub_sq_le_two (hb x) (hb y)).trans
    (mul_le_mul_of_nonneg_left (show |f x-f y|≤(K:ℝ)*|x-y| from by
      simpa only [Real.dist_eq] using hf.dist_le_mul x y) (by norm_num))
  nlinarith

theorem unitBoundedSquare_tendstoUniformly {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n x,|F n x|≤1) (hf : ∀ x,|f x|≤1)
    (hU : TendstoUniformly F f atTop) :
    TendstoUniformly (fun n x => (F n x)^2) (fun x => (f x)^2) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hU (ε/2) (by positivity)] with n hn
  intro x
  have H := abs_sq_sub_sq_le_two (hF n x) (hf x)
  have Hn := hn x
  simp only [Real.dist_eq] at Hn ⊢
  rw [abs_sub_comm] at Hn ⊢
  linarith

def scalarCDFSusceptibilitySquareAverage (β : ℝ) (α : ℝ → ℝ) (r : ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal r)
    (scalarCDFValue β α r (Real.toNNReal (1-r)))
    (fun x => (scalarCDFHessian β α r (Real.toNNReal (1-r)) x)^2) 0

theorem scalarCDFHessian_square_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t≤1) :
    LipschitzWith (2*susceptibilityLipschitzConstant) (fun x => (scalarCDFHessian β α s t x)^2) :=
  unitBoundedSquare_lipschitz (scalarCDFHessian_lipschitz β ha hm s t ht)
    (scalarCDFHessian_abs_le_one β ha hm s t ht)

theorem scalarCDFHessian_square_bound (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |(scalarCDFHessian β α s t x)^2|≤1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (scalarCDFHessian_abs_le_one β ha hm s t ht x)

theorem scalarCDFSusceptibilitySquareAverage_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    Tendsto (fun n => scalarCDFSusceptibilitySquareAverage β (αn n) r) atTop
      (𝓝 (scalarCDFSusceptibilitySquareAverage β α r)) := by
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr.1]
  have hrs : r+s≤1 := by rw [hs]; linarith
  let f := scalarCDFValue β α r s
  let g := fun x => (scalarCDFHessian β α r s x)^2
  let fn := fun n => scalarCDFValue β (αn n) r s
  let gn := fun n x => (scalarCDFHessian β (αn n) r s x)^2
  have hfU : TendstoUniformly fn f atTop :=
    scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hgU : TendstoUniformly gn g atTop :=
    unitBoundedSquare_tendstoUniformly
      (fun n => scalarCDFHessian_abs_le_one β (hn n) (hnm n) r s hs1)
      (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
      (scalarCDFHessian_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs)
  have hc := scalarCDFAverage_tendsto_cdf_lipschitz β hα hαm hn hnm hD
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_square_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_square_bound β hα hαm r s hs1)
    0 t ht1 le_rfl (by simpa only [zero_add,ht] using hr.2) 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := Real.log (1+ε/8)/2
  have hd : 0<δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have he : Real.exp (2*δ)-1=ε/8 := by
    rw [show 2*δ=Real.log (1+ε/8) by dsimp [δ]; ring,
      Real.exp_log (by linarith : 0<1+ε/8)]
    ring
  filter_upwards [(Metric.tendstoUniformly_iff.mp hfU) δ hd,
    (Metric.tendstoUniformly_iff.mp hgU) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hc) (ε/4) (by positivity)] with n hf hg hcn
  have hfg (z) : |fn n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hf z).le
  have hgg (z) : |gn n z-g z|≤ε/4 := by simpa only [Real.dist_eq,abs_sub_comm] using (hg z).le
  have Ht := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n)
    (scalarCDFValue_regular β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_square_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_square_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_square_bound β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_square_bound β hα hαm r s hs1)
    hd.le hfg hgg 0 t ht1 0
  rw [he,NNReal.coe_one] at Ht
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β (αn n) 0 t f g 0|≤_ at Ht
  change dist (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)<ε/4 at hcn
  rw [Real.dist_eq] at hcn
  rw [Real.dist_eq]
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β α 0 t f g 0|<ε
  have H := abs_sub_le (scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0)
    (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)
  linarith

end SK.Analytic

end
end

end OAI
