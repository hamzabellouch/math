import Mathlib
import OAI.Analysis.Conductivity.Sobolev.IntervalTraceEnergy

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma complex_fourier_mode_trace_energy {q : ℝ → ℂ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) {η m : ℝ} (hη : 0<η) (hm : 0 ≤ m) :
    m*‖q 0‖^2≤(1+1/η)*(∫ t in (0:ℝ)..η,
      ‖deriv q t‖^2+(1+m^2)*‖q t‖^2) := by
  have hre := Complex.reCLM.contDiff.comp hq
  have him := Complex.imCLM.contDiff.comp hq
  have hr := fourier_mode_trace_energy hre hη hm
  have hi := fourier_mode_trace_energy him hη hm
  have hdr (t : ℝ) : deriv (fun x => (q x).re) t=(deriv q t).re := by
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      ((hq.differentiable (by simp) t).hasDerivAt)).deriv
  have hdi (t : ℝ) : deriv (fun x => (q x).im) t=(deriv q t).im := by
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      ((hq.differentiable (by simp) t).hasDerivAt)).deriv
  have hd := hq.continuous_deriv (by simp)
  have hInt : (∫ t in (0:ℝ)..η, ‖deriv q t‖^2+(1+m^2)*‖q t‖^2)=
      (∫ t in (0:ℝ)..η, ((deriv q t).re)^2+(1+m^2)*(q t).re^2)+
      (∫ t in (0:ℝ)..η, ((deriv q t).im)^2+(1+m^2)*(q t).im^2) := by
    have hir : IntervalIntegrable (fun t => ((deriv q t).re)^2+(1+m^2)*(q t).re^2) volume 0 η :=
      (((Complex.continuous_re.comp hd).pow 2).add
        (continuous_const.mul ((Complex.continuous_re.comp hq.continuous).pow 2))).intervalIntegrable 0 η
    have hii : IntervalIntegrable (fun t => ((deriv q t).im)^2+(1+m^2)*(q t).im^2) volume 0 η :=
      (((Complex.continuous_im.comp hd).pow 2).add
        (continuous_const.mul ((Complex.continuous_im.comp hq.continuous).pow 2))).intervalIntegrable 0 η
    rw [←intervalIntegral.integral_add hir hii]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp only [←sq]
    ring
  change m*(q 0).re^2 ≤ (1+1/η)*(∫ t in (0:ℝ)..η,
    (deriv (fun x => (q x).re) t)^2+(1+m^2)*(q t).re^2) at hr
  change m*(q 0).im^2 ≤ (1+1/η)*(∫ t in (0:ℝ)..η,
    (deriv (fun x => (q x).im) t)^2+(1+m^2)*(q t).im^2) at hi
  simp only [hdr] at hr
  simp only [hdi] at hi
  rw [hInt,Complex.sq_norm,Complex.normSq_apply]
  simp only [←sq]
  nlinarith

lemma poisson_mode_energy {m : ℝ} (hm : 0 ≤ m) (a : ℂ) :
    IntegrableOn (fun t : ℝ => 2*m^2*Real.exp (-2*m*t)*‖a‖^2) (Ioi 0) ∧
    (∫ t in Ioi (0:ℝ), 2*m^2*Real.exp (-2*m*t)*‖a‖^2)=m*‖a‖^2 := by
  rcases hm.eq_or_lt with hm | hm
  · subst m; simp
  · have hn : -2*m<0 := by linarith
    have hi := (integrableOn_exp_mul_Ioi hn 0).const_mul (2*m^2*‖a‖^2)
    have he : (fun t : ℝ => 2*m^2*Real.exp (-2*m*t)*‖a‖^2)=
        (fun t => (2*m^2*‖a‖^2)*Real.exp ((-2*m)*t)) := by funext t; ring
    rw [he]
    refine ⟨hi,?_⟩
    rw [integral_const_mul,integral_exp_mul_Ioi hn 0]
    simp only [mul_zero,Real.exp_zero]
    field_simp

lemma poisson_spectral_energy {ι : Type*} [Countable ι] {m : ι → ℝ}
    (hm : ∀ i,0 ≤ m i) (a : ι → ℂ) (ha : Summable (fun (i : ι) => m i*‖a i‖^2)) :
    (∫ t in Ioi (0:ℝ), ∑' i,2*(m i)^2*Real.exp (-2*m i*t)*‖a i‖^2)=
      ∑' i,m i*‖a i‖^2 := by
  symm
  have he (i : ι) : (∫ t in Ioi (0:ℝ), ‖2*(m i)^2*Real.exp (-2*m i*t)*‖a i‖^2‖)=
      m i*‖a i‖^2 := by
    rw [show (fun t : ℝ => ‖2*(m i)^2*Real.exp (-2*m i*t)*‖a i‖^2‖)=
      (fun t => 2*(m i)^2*Real.exp (-2*m i*t)*‖a i‖^2) from by
        funext t; rw [Real.norm_eq_abs,abs_of_nonneg]; positivity]
    exact (poisson_mode_energy (hm i) (a i)).2
  have hsum : Summable (fun i => ∫ t in Ioi (0:ℝ),
      ‖2*(m i)^2*Real.exp (-2*m i*t)*‖a i‖^2‖) := by simpa only [he] using ha
  simpa only [(poisson_mode_energy (hm _) (a _)).2] using
    integral_tsum_of_summable_integral_norm
      (fun i => (poisson_mode_energy (hm i) (a i)).1) hsum

lemma spectral_trace_summable {ι : Type*} (q : ι → ℝ → ℂ) (m : ι → ℝ)
    (hq : ∀ i,ContDiff ℝ (↑(⊤ : ℕ∞)) (q i)) (hm : ∀ i,0 ≤ m i)
    {η E : ℝ} (hη : 0<η)
    (hE : ∀ F : Finset ι, (∫ t in (0:ℝ)..η, F.sum (fun (i : ι) =>
      ‖deriv (q i) t‖^2+(1+(m i)^2)*‖q i t‖^2)) ≤ E) :
    Summable (fun (i : ι) => m i*‖q i 0‖^2) ∧
      (∑' i,m i*‖q i 0‖^2)≤(1+1/η)*E := by
  have hnon : 0 ≤ (fun (i : ι) => m i*‖q i 0‖^2) := fun i => mul_nonneg (hm i) (sq_nonneg _)
  have hfin (F : Finset ι) : (∑ i ∈ F,m i*‖q i 0‖^2)≤(1+1/η)*E := by
    have hi (i : ι) : IntervalIntegrable (fun t =>
        ‖deriv (q i) t‖^2+(1+(m i)^2)*‖q i t‖^2) volume 0 η := by
      exact (((hq i).continuous_deriv (by simp)).norm.pow 2 |>.add
        (continuous_const.mul ((hq i).continuous.norm.pow 2))).intervalIntegrable 0 η
    calc
      (∑ i ∈ F,m i*‖q i 0‖^2) ≤ ∑ i ∈ F,(1+1/η)*(∫ t in (0:ℝ)..η,
          ‖deriv (q i) t‖^2+(1+(m i)^2)*‖q i t‖^2) :=
        Finset.sum_le_sum fun i _ => complex_fourier_mode_trace_energy (hq i) hη (hm i)
      _=(1+1/η)*(∫ t in (0:ℝ)..η,F.sum (fun (i : ι) =>
          ‖deriv (q i) t‖^2+(1+(m i)^2)*‖q i t‖^2)) := by
        rw [intervalIntegral.integral_finsetSum (fun i _ => hi i),Finset.mul_sum]
      _≤(1+1/η)*E := mul_le_mul_of_nonneg_left (hE F) (by positivity)
  exact ⟨summable_of_sum_le hnon hfin,Real.tsum_le_of_sum_le hnon hfin⟩

end ScalarConductivity

end

end OAI
