import OAI.Analysis.LipschitzHilbert.Fourier.DyadicResolutionSymbol
import OAI.Analysis.LipschitzHilbert.Fourier.LineFrequencyProjection

namespace OAI

/-! Strong L2 resolution by the genuine binary smooth differences. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

def dyadicSchwartzSum (N : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ n∈Finset.range (2*N+1), lineSchwartzProjection dyadicDifference (dyadicResolutionScale N n)
    (dyadicResolutionScale_pos N n).ne' f

theorem dyadicSchwartzSum_fourier (N : ℕ) (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (dyadicSchwartzSum N f) : SchwartzMap ℝ ℂ) eta=
      dyadicResolutionSymbol N eta*(𝓕 f) eta := by
  simp only [dyadicSchwartzSum,FourierTransform.fourier_sum,sum_apply,lineSchwartzProjection_fourier,dyadicResolutionSymbol]
  exact (Finset.sum_mul _ _ _).symm

theorem dyadicSchwartzSum_sub_fourier (N : ℕ) (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ) eta=
      (dyadicResolutionSymbol N eta-1)*(𝓕 f) eta := by
  change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (dyadicSchwartzSum N f-f)) eta=_
  rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,dyadicSchwartzSum_fourier]
  ring

theorem dyadicSchwartzSum_energy_tendsto (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => ∫ x, ‖dyadicSchwartzSum N f x-f x‖^2) atTop (𝓝 0) := by
  have hi : Integrable (fun eta => (9:ℝ)*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2) :=
    (((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)).const_mul 9
  have hh := tendsto_integral_of_dominated_convergence
    (fun eta => (9:ℝ)*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2)
    (F:=fun N eta => ‖(𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ) eta‖^2)
    (f:=fun _ => (0:ℝ))
    (fun N => ((𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ).continuous.measurable.norm.pow_const 2).aestronglyMeasurable)
    hi
    (fun N => Filter.Eventually.of_forall fun eta => by
      rw [Real.norm_of_nonneg (sq_nonneg _),dyadicSchwartzSum_sub_fourier,norm_mul,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have htri := norm_sub_le (dyadicResolutionSymbol N eta) 1
      have hs := dyadicResolutionSymbol_norm N eta
      simp only [norm_one] at htri
      have hn : ‖dyadicResolutionSymbol N eta-1‖≤3 := by linarith
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by norm_num))
    (by
      filter_upwards [volume.ae_ne (0:ℝ)] with eta heta
      have hlim := (((dyadicResolutionSymbol_tendsto eta heta).sub_const 1).mul_const ((𝓕 f) eta)).norm.pow 2
      simpa only [dyadicSchwartzSum_sub_fourier,sub_self,zero_mul,norm_zero,zero_pow (by decide : 2≠0)] using hlim)
  simpa only [SchwartzMap.integral_norm_sq_fourier,sub_apply,integral_zero] using hh

theorem dyadicSchwartzSum_Lp_tendsto (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => (dyadicSchwartzSum N f).toLp 2 volume) atTop (𝓝 (f.toLp 2 volume)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun N : ℕ => dyadicSchwartzSum N f)
    (fun N => (dyadicSchwartzSum N f).memLp 2 volume) f (f.memLp 2 volume)).mpr
  have he (N : ℕ) : eLpNorm ((dyadicSchwartzSum N f : ℝ → ℂ)-(f : ℝ → ℂ)) 2 volume=
      ENNReal.ofReal (Real.sqrt (∫ x, ‖dyadicSchwartzSum N f x-f x‖^2)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      (((dyadicSchwartzSum N f).memLp 2 volume).sub (f.memLp 2 volume))]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp (dyadicSchwartzSum_energy_tendsto f))
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using hh

def dyadicLineL2Sum (N : ℕ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ n∈Finset.range (2*N+1), lineL2Projection dyadicDifference (dyadicResolutionScale N n)
    (dyadicResolutionScale_pos N n).ne'

theorem dyadicLineL2Sum_onSchwartz (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    dyadicLineL2Sum N (f.toLp 2 volume)=(dyadicSchwartzSum N f).toLp 2 volume := by
  simp only [dyadicLineL2Sum,sum_apply,lineL2Projection_onSchwartz]
  exact (map_sum (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ _).symm

theorem dyadicSchwartzSum_norm (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖(dyadicSchwartzSum N f).toLp 2 volume‖≤2*‖f.toLp 2 volume‖ := by
  have hi := ((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have ho := ((𝓕 (dyadicSchwartzSum N f) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hh := integral_mono ho (hi.const_mul 4) (fun eta => by
    change ‖(𝓕 (dyadicSchwartzSum N f) : SchwartzMap ℝ ℂ) eta‖^2≤4*‖(𝓕 f) eta‖^2
    rw [dyadicSchwartzSum_fourier,norm_mul,mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (pow_le_pow_left₀ (norm_nonneg _) (dyadicResolutionSymbol_norm N eta) 2).trans_eq (by norm_num))
  rw [integral_const_mul,SchwartzMap.integral_norm_sq_fourier,SchwartzMap.integral_norm_sq_fourier] at hh
  have hnorm := memLp_toL2_norm_sq volume (dyadicSchwartzSum N f) ((dyadicSchwartzSum N f).memLp 2 volume)
  have hfnorm := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖(dyadicSchwartzSum N f).toLp 2 volume‖^2=_ at hnorm
  change ‖f.toLp 2 volume‖^2=_ at hfnorm
  rw [←hnorm,←hfnorm] at hh
  nlinarith only [hh,norm_nonneg ((dyadicSchwartzSum N f).toLp 2 volume),norm_nonneg (f.toLp 2 volume)]

theorem dyadicLineL2Sum_bound (N : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖dyadicLineL2Sum N f‖≤2*‖f‖ := by
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [dyadicLineL2Sum_onSchwartz]
  exact dyadicSchwartzSum_norm N g

theorem dyadicLineL2Sum_tendsto (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun N : ℕ => dyadicLineL2Sum N f) atTop (𝓝 f) := by
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨g,hg⟩ := hd.exists_dist_lt f (show 0<eps/8 by positivity)
  have hlim : Tendsto (fun N : ℕ => dyadicLineL2Sum N (g.toLp 2 volume)) atTop (𝓝 (g.toLp 2 volume)) := by
    simpa only [dyadicLineL2Sum_onSchwartz] using dyadicSchwartzSum_Lp_tendsto g
  filter_upwards [(Metric.tendsto_nhds.mp hlim) (eps/2) (by positivity)] with N hN
  have hT := dyadicLineL2Sum_bound N (f-g.toLp 2 volume)
  rw [map_sub] at hT
  have hfinal := norm_add_le (dyadicLineL2Sum N f-dyadicLineL2Sum N (g.toLp 2 volume))
    (dyadicLineL2Sum N (g.toLp 2 volume)-f)
  have hmid := norm_add_le (dyadicLineL2Sum N (g.toLp 2 volume)-g.toLp 2 volume) (g.toLp 2 volume-f)
  rw [sub_add_sub_cancel] at hfinal hmid
  simp only [dist_eq_norm] at hg hN ⊢
  rw [norm_sub_rev f (g.toLp 2 volume)] at hg hT
  linarith only [hfinal,hmid,hT,hN,hg,heps]

end LipschitzHilbert.PacketRepresentation

end

end OAI
