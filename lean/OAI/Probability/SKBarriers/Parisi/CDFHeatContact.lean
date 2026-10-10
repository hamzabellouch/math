import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFEndpoint
import OAI.Probability.SKBarriers.Parisi.CDFPotential
import OAI.Probability.SKBarriers.Gaussian.GaussianHeatVariance
import OAI.Probability.SKBarriers.Gaussian.GaussianPoincare

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_heat_increment_lower (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0) :
    β^2*(q-s)*(∫ z, (gaussianHeat (β*Real.sqrt (q-s))
      (scalarCDFHessian β α q (Real.toNNReal (1-q))) (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)  ≤
      scalarCDFOverlap β α q-scalarCDFOverlap β α s := by
  have hr : Real.toNNReal (1-q)  ≤  1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hu := scalarCDFGradient_hasDerivAt β ha α.mono q _ hr
  have hc := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hb (x : ℝ) := (scalarCDF_derivative_bounds β ha α.mono q _ hr x).1
  have hdf (x : ℝ) : |scalarCDFHessian β α q (Real.toNNReal (1-q)) x|  ≤  1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (scalarCDFGradient β α q (Real.toNNReal (1-q)) x)]
  have he : (β*Real.sqrt q)^2=(β*Real.sqrt s)^2+(β*Real.sqrt (q-s))^2 := by
    simp only [mul_pow,Real.sq_sqrt (hs.trans hsq),Real.sq_sqrt hs,Real.sq_sqrt (sub_nonneg.mpr hsq)]
    ring
  have H := gaussianHeat_variance_integral_lower hu hc zero_le_one zero_le_one hb hdf
    (β*Real.sqrt (q-s)) (β*Real.sqrt s) (β*Real.sqrt q) he
  have HG := scalarCDFGradient_heat_prefix β α ha h1 hs hsq hq
    (fun z hz' => hz z ⟨hs.trans hz'.1,hz'.2⟩)
  rw [scalarCDFOverlap_heat_prefix β ha α.mono ⟨hs.trans hsq,hq⟩ hz,
    scalarCDFOverlap_heat_prefix β ha α.mono ⟨hs,hsq.trans hq⟩
      (fun z hz' => hz z ⟨hz'.1,hz'.2.trans_le hsq⟩),HG]
  simpa only [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hsq)] using H

theorem scalarCDFHeatContact_chi_sq_gt (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0)
    (hcontact : scalarCDFOverlap β α q=q) :
    1 < β^2*(∫ z, (scalarCDFHessian β α q (Real.toNNReal (1-q))
      (β*Real.sqrt q*z))^2 ∂gaussianReal 0 1) := by
  let f : ℝ → ℝ := scalarCDFGradient β α q (Real.toNNReal (1-q))
  let df : ℝ → ℝ := scalarCDFHessian β α q (Real.toNNReal (1-q))
  let k : ℝ := β*Real.sqrt q
  have hr : Real.toNNReal (1-q)  ≤  1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hd (x : ℝ) : HasDerivAt f (df x) x := scalarCDFGradient_hasDerivAt β ha α.mono q _ hr x
  have hc : Continuous df := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hb (x : ℝ) : |f x|  ≤  1 := (scalarCDF_derivative_bounds β ha α.mono q _ hr x).1
  have hdf (x : ℝ) : |df x|  ≤  1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (f x)]
  have hmean : (∫ z, f (k*z) ∂gaussianReal 0 1)=0 := by
    have H := congrFun (scalarCDFGradient_heat_prefix β α ha h1 le_rfl hq0.le hq1 hz) 0
    rw [scalarCDFGradient_zero β ha α.mono 0 _ (by simp)] at H
    simpa only [gaussianHeat,sub_zero,zero_add,f,k] using H.symm
  have hsecond : (∫ z, f (k*z)^2 ∂gaussianReal 0 1)=q := by
    simpa only [f,k,scalarCDFOverlap_heat_prefix β ha α.mono ⟨hq0.le,hq1⟩ hz] using hcontact
  have hnonconstant : ¬∃ c, ∀ z, f (k*z)=c := by
    rintro ⟨c,hc⟩
    simp only [hc,integral_const,probReal_univ,one_smul] at hmean hsecond
    rw [hmean,zero_pow (by decide)] at hsecond
    exact hq0.ne' hsecond.symm
  have HD (z : ℝ) : HasDerivAt (fun z => f (k*z)) (k*df (k*z)) z := by
    convert (hd (k*z)).comp z ((hasDerivAt_id z).const_mul k) using 1 <;> first | rfl | ring
  have HP := gaussian_strict_poincare HD (by fun_prop) zero_le_one (abs_nonneg k)
    (fun z => hb (k*z)) (fun z => by
      rw [abs_mul]; simpa only [mul_one] using mul_le_mul_of_nonneg_left (hdf (k*z)) (abs_nonneg k)) hnonconstant
  rw [hmean,hsecond,zero_pow (by decide),sub_zero] at HP
  simp_rw [mul_pow] at HP
  rw [integral_const_mul] at HP
  have hk : k^2=β^2*q := by dsimp [k]; rw [mul_pow,Real.sq_sqrt hq0.le]
  rw [hk] at HP
  change 1 < β^2*(∫ z, df (k*z)^2 ∂gaussianReal 0 1)
  nlinarith

theorem not_min_of_contact_increment {G Γ J : ℝ → ℝ} (hG : Continuous G)
    (hd : ∀ s∈Icc (0:ℝ) 1, HasDerivAt G (s-Γ s) s) (hJ : Continuous J)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hcontact : Γ q=q) (hJq : 1 < J q)
    (hi : ∀ s∈Icc (0:ℝ) q, (q-s)*J s ≤ Γ q-Γ s) :
    ¬∀ r∈Icc (0:ℝ) 1, G q ≤ G r := by
  obtain ⟨ε,hε,hεJ⟩ := Metric.eventually_nhds_iff.mp (hJ.continuousAt.preimage_mem_nhds
    (Ioi_mem_nhds hJq))
  let δ := min (q/2) (ε/2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδq : δ  ≤  q/2 := min_le_left _ _
  have hδε : δ  ≤  ε/2 := min_le_right _ _
  let r := q-δ
  have hr0 : 0  ≤  r := by dsimp [r]; linarith
  have hrq : r < q := by dsimp [r]; linarith
  have hpos {s : ℝ} (hs : s∈Ioo r q) : 0 < s-Γ s := by
    have hs0 : 0  ≤  s := hr0.trans hs.1.le
    have hsJ : 1 < J s := by
      apply hεJ
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hs.2.le)]
      dsimp [r] at hs
      linarith [hs.1]
    have H := hi s ⟨hs0,hs.2.le⟩
    rw [hcontact] at H
    have HH := mul_lt_mul_of_pos_left hsJ (sub_pos.mpr hs.2)
    nlinarith
  have hstrict := strictMonoOn_of_deriv_pos (convex_Icc r q) hG.continuousOn
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s ⟨hr0.trans hs.1.le,hs.2.le.trans hq1⟩).deriv]
      exact hpos hs)
  intro hmin
  exact (not_lt_of_ge (hmin r ⟨hr0,hrq.le.trans hq1⟩))
    (hstrict ⟨le_rfl,hrq.le⟩ ⟨hrq.le,le_rfl⟩ hrq)

theorem heat_increment_coefficient_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (β q : ℝ) :
    Continuous (fun s : ℝ => β^2*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) f
      (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)) := by
  have hp : Continuous (fun s : ℝ => (β*Real.sqrt (q-s),β*Real.sqrt s)) :=
    (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).prodMk
      (continuous_const.mul Real.continuous_sqrt)
  exact continuous_const.mul ((gaussianHeat_sq_average_continuous hf hB hb).comp hp)

theorem scalarCDFPotential_not_min_heat_prefix (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0)
    (hcontact : scalarCDFOverlap β α q=q) :
    ¬∀ r∈Icc (0:ℝ) 1, scalarCDFPotential β α q ≤ scalarCDFPotential β α r := by
  let df : ℝ → ℝ := scalarCDFHessian β α q (Real.toNNReal (1-q))
  let k : ℝ := β*Real.sqrt q
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hc : Continuous df := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hdf (x : ℝ) : |df x| ≤ 1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (scalarCDFGradient β α q (Real.toNNReal (1-q)) x)]
  let J : ℝ → ℝ := fun s => β^2*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) df
    (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)
  have hJ : Continuous J := heat_increment_coefficient_continuous hc zero_le_one hdf β q
  have hJq : 1 < J q := by
    have HJ : J q=β^2*(∫ z, df (k*z)^2 ∂gaussianReal 0 1) := by
      simp [J,gaussianHeat,k]
    rw [HJ]
    exact scalarCDFHeatContact_chi_sq_gt β α ha h1 hq0 hq1 hz hcontact
  have hΓ := scalarCDFOverlap_continuousOn β α ha h1
  apply not_min_of_contact_increment (scalarCDFPotential_continuous hΓ)
    (fun s hs => by simpa only [cdfGradientTest_eq hs] using scalarCDFPotential_hasDerivAt hΓ s)
    hJ hq0 hq1 hcontact hJq
  intro s hs
  have H := scalarCDFOverlap_heat_increment_lower β α ha h1 hs.1 hs.2 hq1 hz
  have HE : (q-s)*J s=β^2*(q-s)*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) df
      (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1) := by dsimp [J]; ring
  rw [HE]
  exact H

end SK.Analytic

end
end

end OAI
