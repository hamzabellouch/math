import OAI.Analysis.LipschitzHilbert.Estimates.HilbertSignFourth
import OAI.Analysis.LipschitzHilbert.Estimates.HilbertFiniteL2
import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionFourth

namespace OAI

/-! Uniform fourth-power bounds for the finite smooth Hilbert kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertFinite_fourth (N : ℕ) (L : ℝ) (hL : 0<L) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x‖^4)≤
      (68*16*Real.pi^4*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4)*
        (∫ x, ‖f x‖^4) := by
  let A := (2*L)/(2:ℝ)^N
  let B := 2*L
  have hA : 0<A := div_pos (mul_pos (by norm_num) hL) (pow_pos (by norm_num) N)
  have hB : 0<B := mul_pos (by norm_num) hL
  let u := lineSchwartzProjection verticalBinPlateau A hA.ne' f-
    lineSchwartzProjection verticalBinPlateau B hB.ne' f
  let H := lineSchwartzProjection (hilbertFiniteSymbol N L hL) 1 (by norm_num) f
  let k : ℂ := -(Real.pi:ℂ)*Complex.I
  have hk : k≠0 := mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let v := k⁻¹ • H
  have hu (eta : ℝ) : (𝓕 u : SchwartzMap ℝ ℂ) eta=
      (verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta := by
    change (𝓕 (lineSchwartzProjection verticalBinPlateau A hA.ne' f-
      lineSchwartzProjection verticalBinPlateau B hB.ne' f) : SchwartzMap ℝ ℂ) eta=_
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,
      add_apply,neg_apply,lineSchwartzProjection_fourier]
    ring
  have huzero : (𝓕 u : SchwartzMap ℝ ℂ) 0=0 := by rw [hu]; simp
  have hv (eta : ℝ) : (𝓕 v : SchwartzMap ℝ ℂ) eta=
      hilbertFrequencySign eta*(𝓕 u : SchwartzMap ℝ ℂ) eta := by
    change (𝓕 (k⁻¹ • H) : SchwartzMap ℝ ℂ) eta=_
    rw [FourierTransform.fourier_smul,smul_apply]
    change k⁻¹*(𝓕 H : SchwartzMap ℝ ℂ) eta=_
    rw [lineSchwartzProjection_fourier,one_mul,hilbertFiniteSymbol_apply,hu]
    change k⁻¹*(k*hilbertFrequencySign eta*
      (verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta)=_
    calc
      _ = (k⁻¹*k)*(hilbertFrequencySign eta*
        ((verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hk,one_mul]
  have hv4 := hilbertSign_fourth_power u v huzero hv
  have hu4 := lineSchwartzProjection_difference_fourth verticalBinPlateau A B hA hB f
  have hH : H=k • v := by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ hk,one_smul]
  have hkn : ‖k‖=Real.pi := by
    simp only [k,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_I,mul_one]
  have heq (x : ℝ) : lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x=H x := by
    dsimp [H]
    rw [lineSchwartzProjection_eq_convolution]
    simp only [lineConvolution,hilbertFinite_kernel]
  simp_rw [heq,hH,smul_apply,norm_smul,hkn,mul_pow]
  rw [integral_const_mul]
  change (∫ x, ‖u x‖^4)≤_ at hu4
  have hp : 0≤Real.pi^4 := pow_nonneg Real.pi_pos.le 4
  calc
    _ ≤ Real.pi^4*(68*(∫ x, ‖u x‖^4)) := mul_le_mul_of_nonneg_left hv4 hp
    _ ≤ Real.pi^4*(68*(16*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4*
        (∫ x, ‖f x‖^4))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hu4 (by norm_num)) hp
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
