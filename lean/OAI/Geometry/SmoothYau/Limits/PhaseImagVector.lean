import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.FrameInverseApply

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

def phaseImagVector (z : Fin 3 → ℂ) : PhaseSpace := WithLp.toLp 2 (fun i => (z i).im)

def normalImagCovector (q : NormalWaveParameter) (z : Fin 3 → ℂ) : NormalWaveSpace →L[ℝ] ℝ :=
  Complex.imCLM.comp (normalPhaseCovector q z)

lemma normalImagCovector_apply (q : NormalWaveParameter) (z : Fin 3 → ℂ) (v : NormalWaveSpace) :
    normalImagCovector q z v = inner ℝ (phaseImagVector z) (q.2.inverse v) := by
  change (normalPhaseCovector q z v).im = _
  rw [normalPhaseCovector_apply]
  simp only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
    phaseImagVector,Pi.star_apply,star_trivial]
  rfl

lemma null_phase_imag_energy {z : Fin 3 → ℂ} (hz : ∑ i, z i*z i = -1) :
    ‖phaseImagVector z‖^2 = 1+‖phaseRealVector z‖^2 := by
  have h := congrArg Complex.re hz
  simp only [Complex.re_sum,Complex.mul_re,Complex.neg_re,Complex.one_re,
    Finset.sum_sub_distrib] at h
  simp only [←pow_two] at h
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i, ((z i).im)^2) = 1+∑ i, ((z i).re)^2
  linarith

lemma normalImagCovector_comp_frame (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (z : Fin 3 → ℂ) :
    (normalImagCovector q z).comp q.2 = InnerProductSpace.toDual ℝ PhaseSpace (phaseImagVector z) := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  ext v
  simp only [ContinuousLinearMap.comp_apply,normalImagCovector_apply,←hA,
    ContinuousLinearMap.inverse_equiv,ContinuousLinearEquiv.coe_coe,
    A.symm_apply_apply,InnerProductSpace.toDual_apply_apply]

lemma normalImagCovector_eq (q : NormalWaveParameter) (z : Fin 3 → ℂ) :
    normalImagCovector q z =
      (InnerProductSpace.toDual ℝ PhaseSpace (phaseImagVector z)).comp q.2.inverse := by
  ext v
  exact normalImagCovector_apply q z v

lemma euclidean_covector_squared_norm (β : PhaseSpace →L[ℝ] ℝ) :
    ‖β‖^2 = ∑ i : Fin 3, (β (EuclideanSpace.basisFun (Fin 3) ℝ i))^2 := by
  let v := (InnerProductSpace.toDual ℝ PhaseSpace).symm β
  have hv : ‖v‖ = ‖β‖ := (InnerProductSpace.toDual ℝ PhaseSpace).symm.norm_map β
  rw [←hv,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hi : v i = β (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
    rw [←EuclideanSpace.inner_basisFun_real]
    exact InnerProductSpace.toDual_symm_apply
  rw [hi]

theorem compact_normal_angular_energy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ,
      (∑ i, z i*z i = -1) →
      c*(1+‖phaseRealVector z‖^2) ≤
        ∑ i : Fin 3, (normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i))^2 ∧
      (∑ i : Fin 3, (normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i))^2) ≤
        C*(1+‖phaseRealVector z‖^2) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_bound g hK
  obtain ⟨S,hS,hi⟩ := metricFrameSet_inverse_bound g hK
  refine ⟨(R^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hR),S^2,sq_pos_of_pos hS,?_⟩
  intro q hq z hz
  have hlo : ‖phaseImagVector z‖ ≤ ‖normalImagCovector q z‖*R := by
    have hh := ContinuousLinearMap.opNorm_comp_le (normalImagCovector q z) q.2
    rw [normalImagCovector_comp_frame g hq z,LinearIsometryEquiv.norm_map] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hb q hq) (norm_nonneg _))
  have hhi : ‖normalImagCovector q z‖ ≤ S*‖phaseImagVector z‖ := by
    rw [normalImagCovector_eq]
    have hh := ContinuousLinearMap.opNorm_comp_le
      (InnerProductSpace.toDual ℝ PhaseSpace (phaseImagVector z)) q.2.inverse
    rw [LinearIsometryEquiv.norm_map] at hh
    exact hh.trans (by nlinarith [hi q hq,norm_nonneg (phaseImagVector z)])
  rw [←euclidean_covector_squared_norm,←null_phase_imag_energy hz]
  constructor
  · have hs : ‖phaseImagVector z‖^2 ≤ ‖normalImagCovector q z‖^2*R^2 := by
      nlinarith [sq_nonneg (‖normalImagCovector q z‖*R-‖phaseImagVector z‖),
        norm_nonneg (phaseImagVector z),norm_nonneg (normalImagCovector q z)]
    calc
      _ ≤ (R^2)⁻¹*(‖normalImagCovector q z‖^2*R^2) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (sq_nonneg R))
      _ = _ := by field_simp
  · nlinarith [sq_nonneg (S*‖phaseImagVector z‖-‖normalImagCovector q z‖),
      norm_nonneg (phaseImagVector z),norm_nonneg (normalImagCovector q z)]
end YauCounterexamples
end

end OAI
