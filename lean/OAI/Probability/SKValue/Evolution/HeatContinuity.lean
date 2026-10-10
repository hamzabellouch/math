import Mathlib
import OAI.Probability.SKValue.Evolution.HeatBounds

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma gaussian_shift_continuous {f : ℝ → ℝ} (hfc : Continuous f) (hfg : ExpGrowth f) :
    Continuous (fun p : ℝ×ℝ ↦ ∫ z, f (p.1+p.2*z) ∂standardGaussian) := by
  obtain ⟨a,C,ha,hC,hf⟩ := hfg
  apply continuous_iff_continuousAt.mpr
  intro p
  let bd := fun z ↦ (C*Real.exp (a*(|p.1|+1)))*Real.exp ((a*(|p.2|+1))* |z|)
  apply tendsto_integral_filter_of_dominated_convergence bd
    (Eventually.of_forall (fun q ↦ by fun_prop)) _
    ((gaussian_exp_abs_integrable (a*(|p.2|+1))).const_mul _) _
  · filter_upwards [Metric.ball_mem_nhds p (by norm_num : (0 : ℝ)<1)] with q hq
    have hq' : |q.1-p.1|<1 ∧ |q.2-p.2|<1 := by
      simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,max_lt_iff] using hq
    have hq1 : |q.1|≤|p.1|+1 := by
      have hh := abs_add_le (q.1-p.1) p.1
      rw [sub_add_cancel] at hh
      linarith [hq'.1]
    have hq2 : |q.2|≤|p.2|+1 := by
      have hh := abs_add_le (q.2-p.2) p.2
      rw [sub_add_cancel] at hh
      linarith [hq'.2]
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    apply (expGrowth_shift_bound ha hC hf q.1 q.2 z).trans
    dsimp only [bd]
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq1 ha)) hC)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 ha) (abs_nonneg z)))
      (Real.exp_pos _).le (by positivity)
  · exact Eventually.of_forall (fun z ↦ (hfc.comp (continuous_fst.add (continuous_snd.mul continuous_const))).continuousAt)

lemma heat_continuous {f : ℝ → ℝ} (hfc : Continuous f) (hfg : ExpGrowth f) :
    Continuous (fun p : ℝ×ℝ ↦ heat p.1 f p.2) := by
  exact (gaussian_shift_continuous hfc hfg).comp
    (continuous_snd.prodMk (Real.continuous_sqrt.comp continuous_fst))

@[simp] lemma heat_zero (f : ℝ → ℝ) (x : ℝ) : heat 0 f x=f x := by
  simp [heat]

@[simp] lemma coleHopf_zero_coeff (h : ℝ) (ψ : ℝ → ℝ) : coleHopf 0 h ψ=heat h ψ := by
  funext x
  simp [coleHopf]

@[simp] lemma coleHopf_zero (c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : coleHopf c 0 ψ x=ψ x := by
  by_cases hc : c=0
  · simp [coleHopf,hc]
  · simp [coleHopf,hc,Real.log_exp]

lemma coleHopf_continuous {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {c : ℝ} (hc : 0≤c) :
    Continuous (fun p : ℝ×ℝ ↦ coleHopf c p.1 ψ p.2) := by
  by_cases hc0 : c=0
  · simpa [SKValue.coleHopf,hc0] using heat_continuous hψ.continuous (ExpGrowth.lipschitz hψ)
  · have hH := heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.continuous)) (ExpGrowth.exp_lipschitz hψ hc)
    simpa only [coleHopf,ite_eq_right hc0,Function.comp_def,Pi.mul_apply] using
      (hH.log (fun p ↦ (lipschitz_exp_integral_pos hψ hc p.2 (Real.sqrt p.1)).ne')).div_const c

lemma heat_bound {f : ℝ → ℝ} {C : ℝ} (hC : 0≤C) (hf : ∀ x, |f x|≤C) (h x : ℝ) :
    |heat h f x|≤C := by
  unfold heat
  by_cases hfi : Integrable (fun z ↦ f (x+Real.sqrt h*z)) standardGaussian
  · apply abs_integral_le_integral_abs.trans
    convert integral_mono hfi.abs
      (integrable_const C : Integrable (fun _ : ℝ ↦ C) standardGaussian)
      (fun z ↦ hf (x+Real.sqrt h*z)) using 1
    simp
  · simpa only [integral_undef hfi,abs_zero] using hC

structure SmoothTerminal (ψ : ℝ → ℝ) : Prop where
  lipschitz : LipschitzWith 1 ψ
  smooth : ContDiff ℝ ∞ ψ
  jets : BoundedSmooth (deriv ψ)

lemma SmoothTerminal.growth {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (n : ℕ) :
    ExpGrowth (iteratedDeriv n ψ) := by
  cases n with
  | zero => simpa only [iteratedDeriv_zero] using ExpGrowth.lipschitz hψ.lipschitz
  | succ n =>
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    rw [iteratedDeriv_succ']
    exact ExpGrowth.of_bound hC hb

lemma SmoothTerminal.heat_smooth {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (h : ℝ) :
    ContDiff ℝ ∞ (heat h ψ) := heat_contDiff hψ.smooth hψ.growth h

lemma SmoothTerminal.heat_deriv {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (h : ℝ) :
    deriv (heat h ψ)=heat h (deriv ψ) := by
  simpa only [iteratedDeriv_one] using heat_iteratedDeriv hψ.smooth hψ.growth h 1

lemma SmoothTerminal.heat_deriv_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (n : ℕ) (h : ℝ) :
    iteratedDeriv n (deriv (heat h ψ))=heat h (iteratedDeriv n (deriv ψ)) := by
  simpa only [iteratedDeriv_succ'] using heat_iteratedDeriv hψ.smooth hψ.growth h (n+1)

lemma SmoothTerminal.coleHopf_smooth {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0≤c) (h : ℝ) :
    ContDiff ℝ ∞ (coleHopf c h ψ) := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [coleHopf_zero_coeff]
    exact hψ.heat_smooth h
  · exact coleHopf_contDiff_of_pos hψ.lipschitz hψ.smooth hψ.jets hc h

lemma SmoothTerminal.coleHopf_deriv_bound {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0≤c) (h x : ℝ) :
    |deriv (coleHopf c h ψ) x|≤1 := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [coleHopf_zero_coeff]
    rw [hψ.heat_deriv]
    apply heat_bound zero_le_one
    intro y
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ.lipschitz (x₀ := y)
  · exact coleHopf_deriv_bound_of_pos hψ.lipschitz
      (hψ.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hc h x

lemma SmoothTerminal.evolve {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0≤c) (h : ℝ) :
    SmoothTerminal (coleHopf c h ψ) := by
  have hs := hψ.coleHopf_smooth hc h
  refine ⟨?_,hs,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)))
    intro x
    exact_mod_cast hψ.coleHopf_deriv_bound hc h x
  · rcases hc.eq_or_lt with rfl | hc
    · refine ⟨(contDiff_infty_iff_deriv.mp hs).2,?_⟩
      intro n
      obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
      refine ⟨C,hC,?_⟩
      intro x
      rw [coleHopf_zero_coeff]
      rw [hψ.heat_deriv_jets]
      exact heat_bound hC hb h x
    · exact coleHopf_deriv_boundedSmooth_of_pos hψ.lipschitz hψ.smooth hψ.jets hc h

lemma SmoothTerminal.coleHopf_uniform_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0≤c) :
    ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ h x, |iteratedDeriv n (deriv (coleHopf c h ψ)) x|≤C := by
  rcases hc.eq_or_lt with rfl | hc
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    refine ⟨C,hC,?_⟩
    intro h x
    rw [coleHopf_zero_coeff]
    rw [hψ.heat_deriv_jets]
    exact heat_bound hC hb h x
  · exact coleHopf_deriv_uniform_bounds_of_pos hψ.lipschitz hψ.smooth hψ.jets hc

end SKValue

end

end OAI
