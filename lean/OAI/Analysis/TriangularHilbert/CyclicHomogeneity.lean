import OAI.Analysis.TriangularHilbert.CyclicMaxMoment

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat Filter
open scoped ENNReal
noncomputable section

def cyclicNorm (B C : Plane → ℂ) : ℝ≥0∞ :=
  (∫⁻ z : Plane, cyclicMax B C z ^ ((3:ℝ)/2)) ^ ((2:ℝ)/3)

lemma cyclicKernelOutput_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    ∀ᵐ z : Plane, ∀ K : ℝ → ℝ, cyclicKernelOutput B C K z = cyclicKernelOutput B' C' K z := by
  filter_upwards [quasiMeasurePreserving_snd.ae (ae_ae_of_ae_prod hb),
    quasiMeasurePreserving_fst.ae (ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hc))]
    with z hzB hzC
  intro K
  apply integral_congr_ae
  filter_upwards [hzB,hzC] with c hB hC
  change C (c,z.1) = C' (c,z.1) at hC
  simp only [hB,hC]

lemma cyclicMax_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    cyclicMax B C =ᵐ[volume] cyclicMax B' C' := by
  filter_upwards [cyclicKernelOutput_congr_ae hb hc] with z hz
  simp only [cyclicMax,hz]

lemma cyclicNorm_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    cyclicNorm B C = cyclicNorm B' C' := by
  unfold cyclicNorm
  congr 1
  apply lintegral_congr_ae
  filter_upwards [cyclicMax_congr_ae hb hc] with z hz
  rw [hz]

@[simp] lemma cyclicNorm_zero_left (C : Plane → ℂ) : cyclicNorm 0 C = 0 := by
  simp [cyclicNorm,cyclicMax,cyclicKernelOutput]
@[simp] lemma cyclicNorm_zero_right (B : Plane → ℂ) : cyclicNorm B 0 = 0 := by
  simp [cyclicNorm,cyclicMax,cyclicKernelOutput]

lemma cyclicKernelOutput_smul (B C : Plane → ℂ) (u v : ℂ) (K : ℝ → ℝ) (z : Plane) :
    cyclicKernelOutput (u • B) (v • C) K z = (u*v)*cyclicKernelOutput B C K z := by
  rw [cyclicKernelOutput,cyclicKernelOutput,← integral_const_mul]
  congr 1
  funext c
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

lemma cyclicMax_smul (B C : Plane → ℂ) (u v : ℂ) (z : Plane) :
    cyclicMax (u • B) (v • C) z = (‖u‖ₑ*‖v‖ₑ)*cyclicMax B C z := by
  simp only [cyclicMax,cyclicKernelOutput_smul,ofReal_norm,enorm_mul]
  rw [ENNReal.mul_iSup]

lemma cyclicNorm_smul (B C : Plane → ℂ) (u v : ℂ) :
    cyclicNorm (u • B) (v • C) = (‖u‖ₑ*‖v‖ₑ)*cyclicNorm B C := by
  have he : (fun z : Plane => cyclicMax (u • B) (v • C) z ^ ((3:ℝ)/2)) =
      (fun z : Plane => (‖u‖ₑ*‖v‖ₑ)^((3:ℝ)/2)*cyclicMax B C z^((3:ℝ)/2)) := by
    funext z
    rw [cyclicMax_smul,ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [cyclicNorm,cyclicNorm,he,
    lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),← ENNReal.rpow_mul]
  norm_num
end
end TriangularHilbert
end

end OAI
