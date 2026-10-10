import OAI.Analysis.LipschitzHilbert.Estimates.SmoothCarlesonEstimate

namespace OAI

/-! The smooth Carleson estimate in real squared L2 energy, for the
actual high/low convolution products. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def smoothDyadicProduct (f : ℝ → ℂ) (h : SchwartzMap ℝ ℂ)
    (ratio : ℝ) (hratio : 0<ratio) (k : ℤ) (x : ℝ) : ℂ :=
  lineConvolution (lineProjectionKernel dyadicDifference (scale k) (scale_pos _).ne') f x*
    lineConvolution (lineProjectionKernel reassemblyLow (ratio*scale k)
      (mul_pos hratio (scale_pos _)).ne') h x

theorem smoothDyadicProduct_measurable (f : ℝ → ℂ) (hfm : Measurable f)
    (h : SchwartzMap ℝ ℂ) (ratio : ℝ) (hratio : 0<ratio) (k : ℤ) :
    Measurable (smoothDyadicProduct f h ratio hratio k) :=
  (lineConvolution_measurable _ (lineProjectionKernel _ _ _).continuous.measurable f hfm).mul
    (lineConvolution_measurable _ (lineProjectionKernel _ _ _).continuous.measurable h h.continuous.measurable)

theorem smoothDyadicProduct_energy_eq (f : ℝ → ℂ) (h : SchwartzMap ℝ ℂ)
    (ratio : ℝ) (hratio : 0<ratio) (k : ℤ) :
    (∫⁻ x, ENNReal.ofReal (‖smoothDyadicProduct f h ratio hratio k x‖^2))=
      ∫⁻ x, ENNReal.ofReal (‖lineConvolution
        (lineProjectionKernel dyadicDifference (scale k) (scale_pos _).ne') f x‖^2)*
      ENNReal.ofReal (‖lineConvolution
        (lineProjectionKernel reassemblyLow (ratio*scale k) (mul_pos hratio (scale_pos _)).ne') h x‖^2) := by
  apply lintegral_congr
  intro x
  simp only [smoothDyadicProduct,norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _)]

theorem smooth_carleson_energy (I : Finset ℤ)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (ratio : ℝ) (hratio : 0<ratio) (h : SchwartzMap ℝ ℂ) :
    (∀ k∈I, MemLp (smoothDyadicProduct f h ratio hratio k) 2 volume) ∧
    (∑ k∈I, ∫ x, ‖smoothDyadicProduct f h ratio hratio k x‖^2)≤
      36*dyadicCarlesonConstant*(lineCellMaximalConstant reassemblyLow ratio)^2*B^2*
        (∫ x, ‖h x‖^2) := by
  let E := lineCellMaximalConstant reassemblyLow ratio
  let C := 36*dyadicCarlesonConstant*E^2*B^2*(∫ x, ‖h x‖^2)
  have hE : 0≤E := lineCellMaximalConstant_nonneg _ _ hratio
  have hCb : 0≤dyadicCarlesonConstant*B^2 :=
    mul_nonneg dyadicCarlesonConstant_pos.le (sq_nonneg B)
  have hC : 0≤C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      dyadicCarlesonConstant_pos.le) (sq_nonneg E)) (sq_nonneg B))
      (integral_nonneg (fun _ => sq_nonneg _))
  have hg := smooth_carleson_estimate I f hfm B hB hfb ratio hratio h
  have hrhs : ENNReal.ofReal (dyadicCarlesonConstant*B^2)*ENNReal.ofReal E^2*
      ENNReal.ofReal (36*(∫ x, ‖h x‖^2))=ENNReal.ofReal C := by
    rw [←ENNReal.ofReal_pow hE,←ENNReal.ofReal_mul hCb,
      ←ENNReal.ofReal_mul (mul_nonneg hCb (sq_nonneg E))]
    congr 1
    dsimp [C]
    ring
  change (∑ k∈I, _)≤ENNReal.ofReal (dyadicCarlesonConstant*B^2)*ENNReal.ofReal E^2*
    ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) at hg
  rw [hrhs] at hg
  simp_rw [←smoothDyadicProduct_energy_eq f h ratio hratio] at hg
  have hi (k : ℤ) (hk : k∈I) : Integrable (fun x => ‖smoothDyadicProduct f h ratio hratio k x‖^2) := by
    have hfin : (∫⁻ x, ENNReal.ofReal (‖smoothDyadicProduct f h ratio hratio k x‖^2))≠⊤ :=
      ne_of_lt ((Finset.single_le_sum (fun _ _ => bot_le) hk).trans_lt
        (hg.trans_lt ENNReal.ofReal_lt_top))
    have hm := ((smoothDyadicProduct_measurable f hfm h ratio hratio k).norm.pow_const 2).ennreal_ofReal
    have hh := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hh
  constructor
  · intro k hk
    exact (memLp_two_iff_integrable_sq_norm
      (smoothDyadicProduct_measurable f hfm h ratio hratio k).aestronglyMeasurable).mpr (hi k hk)
  · have he : (∑ k∈I, ENNReal.ofReal (∫ x, ‖smoothDyadicProduct f h ratio hratio k x‖^2))=
        ∑ k∈I, ∫⁻ x, ENNReal.ofReal (‖smoothDyadicProduct f h ratio hratio k x‖^2) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact ofReal_integral_eq_lintegral_ofReal (hi k hk) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    rw [←he,←ENNReal.ofReal_sum_of_nonneg (fun k _ => integral_nonneg (fun _ => sq_nonneg _))] at hg
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
    simpa only [ENNReal.toReal_ofReal hC,
      ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))] using ht

end LipschitzHilbert.PacketRepresentation

end

end OAI
