import OAI.Analysis.LipschitzHilbert.Estimates.SharpHilbertThird
import OAI.Analysis.LipschitzHilbert.Estimates.HalfPowerDualTest
import OAI.Analysis.LipschitzHilbert.Fourier.ConvolutionBasicL1
import OAI.Analysis.LipschitzHilbert.Estimates.CubicDualityEstimate

namespace OAI

/-! Uniform three-halves estimates by the explicit dual test and the
proved third-moment bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_odd (r R t : ℝ) : sharpTimeKernel r R (-t)= -sharpTimeKernel r R t := by
  unfold sharpTimeKernel
  simp only [abs_neg]
  split_ifs <;> simp

theorem sharpHilbert_uniform_three_halves : ∃ C : ℝ, 0<C ∧
    ∀ r R : ℝ, 0<r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^(3/2:ℝ)) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^(3/2:ℝ))≤
        C^(3/2:ℝ)*(∫ x, ‖f x‖^(3/2:ℝ)) := by
  obtain ⟨E,hE,hThird⟩ := sharpHilbert_uniform_third_bounded
  obtain ⟨A,hA,hTwo⟩ := sharpHilbert_uniform_L2
  refine ⟨E+1,by positivity,?_⟩
  intro r R hr hrR f
  let K := sharpTimeKernel r R
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hKm : Measurable K := sharpTimeKernel_measurable r R
  let g := oneDimensionalTruncatedHilbert r R f
  have hgm : Measurable g := lineConvolution_measurable K hKm f f.continuous.measurable
  have hg1 : Integrable g := lineConvolution_integrable K f hKi f.integrable
  have hg2 : MemLp g 2 volume := (hTwo r R hr hrR f).1
  let B := (∫ t, ‖K t‖)*SchwartzMap.seminorm ℝ 0 0 f
  have hgb (x : ℝ) : ‖g x‖≤B := lineConvolution_bound K f hKi
    (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x
  let h := halfPowerDualTest g
  have hhm : Measurable h := halfPowerDualTest_measurable g hgm
  have hhp := halfPowerDualTest_memLp g hgm hg1 hg2
  have hhb (x : ℝ) : ‖h x‖≤B+1 := halfPowerDualTest_bound g B hgb x
  have hh3 : Integrable (fun x => ‖h x‖^3) := memLp_two_four_integrable_cube h hhm hhp.1 hhp.2
  have hgi : Integrable (fun x => ‖g x‖^(3/2:ℝ)) := by
    simpa only [h,halfPowerDualTest_norm_cube] using hh3
  let J := ∫ x, ‖g x‖^(3/2:ℝ)
  let F := ∫ x, ‖f x‖^(3/2:ℝ)
  have hJ : 0≤J := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hF : 0≤F := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  let v := oneDimensionalTruncatedHilbert r R h
  have hvm : Measurable v := lineConvolution_measurable K hKm h hhm
  have hvBound := hThird r R hr hrR h hhm hhp.1 hhp.2 (B+1) hhb
  have hv3 : MemLp v (ENNReal.ofReal (3:ℝ)) volume := by
    have hh : MemLp v 3 volume := (integrable_norm_rpow_iff hvm.aestronglyMeasurable
      (by norm_num : (3:ℝ≥0∞)≠0) (by norm_num)).mp (by simpa using hvBound.1)
    simpa using hh
  have hvEnergy : (∫ x, ‖v x‖^3)≤E*J := by
    simpa only [h,halfPowerDualTest_norm_cube] using hvBound.2
  have hpair := lineConvolution_pairing K f (fun x => conj (h x)) hKi hKm
    f.integrable f.continuous.measurable (by fun_prop) (B+1)
    (fun x => by simpa only [Complex.norm_conj] using hhb x)
  have hleft : (∫ x, g x*conj (h x))=(J:ℂ) := by
    simp only [h,halfPowerDualTest_pair,integral_complex_ofReal]
    rfl
  have hright : (∫ x, f x*reverseLineConvolution K (fun y => conj (h y)) x)=
      -(∫ x, f x*conj (v x)) := by
    simp_rw [reverseLineConvolution_conj K h (sharpTimeKernel_odd r R)
      (sharpTimeKernel_conj r R),mul_neg,integral_neg]
    rfl
  have hidentity : (J:ℂ)= -(∫ x, f x*conj (v x)) := hleft.symm.trans (hpair.trans hright)
  have hnorm : J=‖∫ x, f x*conj (v x)‖ := by
    have hh := congrArg norm hidentity
    simpa only [Complex.norm_real,Real.norm_of_nonneg hJ,norm_neg] using hh
  have hhold := integral_mul_norm_le_Lp_mul_Lq (p:=3/2) (q:=3)
    (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    (f.memLp (ENNReal.ofReal (3/2:ℝ)) volume) hv3
  have hi : J≤F^(2/3:ℝ)*(∫ x, ‖v x‖^3)^(1/3:ℝ) := by
    calc
      J = ‖∫ x, f x*conj (v x)‖ := hnorm
      _ ≤ ∫ x, ‖f x*conj (v x)‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖*‖v x‖ := by simp only [norm_mul,Complex.norm_conj]
      _ ≤ _ := by simpa only [show (1/(3/2):ℝ)=2/3 by norm_num,Real.rpow_ofNat] using hhold
  refine ⟨hgi,?_⟩
  exact cubic_duality_estimate F J E hF hJ hE (hi.trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (integral_nonneg fun x => by positivity) hvEnergy (by norm_num))
      (Real.rpow_nonneg hF _)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
