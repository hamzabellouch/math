import OAI.Analysis.LipschitzHilbert.Fourier.AnnularResolutionSymbols
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinReconstruction
import OAI.Analysis.LipschitzHilbert.Estimates.CompactMollificationL2

namespace OAI

/-! Strong L2 resolution of a Schwartz function by the concrete finite
vertical annular sums. The zero vertical frequency is a null set. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

def schwartzAnnularSum (N : ℕ) (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  ∑ n∈Finset.range (2*N+1),
    schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f

theorem schwartzAnnularSum_fourier (N : ℕ) (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (schwartzAnnularSum N f) omega=
      reassemblySymbol N omega.2*planarFourier f omega := by
  unfold schwartzAnnularSum
  rw [planarFourier_schwartz_sum]
  simp only [schwartzVerticalProjection_fourier,sub_zero,reassemblyDifferenceSchwartz_apply]
  exact (Finset.sum_mul _ _ _).symm

theorem schwartzAnnularSum_sub_fourier (N : ℕ) (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (schwartzAnnularSum N f-f : SchwartzMap (ℝ×ℝ) ℂ) omega=
      (reassemblySymbol N omega.2-1)*planarFourier f omega := by
  rw [planarFourier_sub,schwartzAnnularSum_fourier]
  ring

theorem schwartzAnnularSum_energy_tendsto (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Tendsto (fun N : ℕ => ∫ z, ‖schwartzAnnularSum N f z-f z‖^2 ∂planeMeasure)
      atTop (𝓝 0) := by
  have hdom : Integrable (fun omega => (9:ℝ)*‖planarFourier f omega‖^2) planeMeasure := by
    have h := ((planarFourierSchwartz f).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
    simpa only [planarFourierSchwartz_apply] using h.const_mul 9
  have h := tendsto_integral_of_dominated_convergence (μ:=planeMeasure)
    (fun omega => (9:ℝ)*‖planarFourier f omega‖^2)
    (F:=fun N omega => ‖planarFourier (schwartzAnnularSum N f-f : SchwartzMap (ℝ×ℝ) ℂ) omega‖^2)
    (f:=fun _ => (0:ℝ))
    (fun N => by
      simpa only [planarFourierSchwartz_apply] using
        ((planarFourierSchwartz (schwartzAnnularSum N f-f)).continuous.measurable.norm.pow_const 2).aestronglyMeasurable)
    hdom
    (fun N => Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_of_nonneg (sq_nonneg _),schwartzAnnularSum_sub_fourier,norm_mul,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hnorm : ‖reassemblySymbol N omega.2-1‖≤3 := by
        have htri := norm_sub_le (reassemblySymbol N omega.2) 1
        simp only [norm_one] at htri
        linarith only [htri,reassemblySymbol_norm N omega.2]
      nlinarith only [sq_nonneg ‖reassemblySymbol N omega.2-1‖,hnorm,norm_nonneg (reassemblySymbol N omega.2-1)])
    (by
      have hne : ∀ᵐ omega : ℝ×ℝ ∂planeMeasure, omega.2≠0 :=
        Measure.quasiMeasurePreserving_snd.ae (volume.ae_ne 0)
      filter_upwards [hne] with omega homega
      have hlim := (((reassemblySymbol_tendsto omega.2 homega).sub_const 1).mul_const
        (planarFourier f omega)).norm.pow 2
      simpa only [sub_self,zero_mul,norm_zero,zero_pow (by decide : 2≠0),
        schwartzAnnularSum_sub_fourier] using hlim)
  simpa only [planar_integral_norm_sq_fourier,sub_apply,integral_zero] using h

theorem schwartzAnnularSum_Lp_tendsto (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Tendsto (fun N : ℕ => (schwartzAnnularSum N f).toLp 2 planeMeasure)
      atTop (𝓝 (f.toLp 2 planeMeasure)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun N : ℕ => schwartzAnnularSum N f)
    (fun N => (schwartzAnnularSum N f).memLp 2 planeMeasure) f (f.memLp 2 planeMeasure)).mpr
  have he (N : ℕ) : eLpNorm ((schwartzAnnularSum N f : (ℝ×ℝ) → ℂ)-(f : (ℝ×ℝ) → ℂ)) 2 planeMeasure=
      ENNReal.ofReal (Real.sqrt (∫ z, ‖schwartzAnnularSum N f z-f z‖^2 ∂planeMeasure)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      (((schwartzAnnularSum N f).memLp 2 planeMeasure).sub (f.memLp 2 planeMeasure))]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp (schwartzAnnularSum_energy_tendsto f))
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
