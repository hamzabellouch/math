import Mathlib
import OAI.Probability.LogConcave.Numerics.CenteringVelocityPicard

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

lemma productPointEquiv_lipschitz_one (d e : ℕ) :
    LipschitzWith 1 (productPointEquiv d e) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,←map_sub]
  rw [Prod.norm_def]
  exact max_le (productPointEquiv_fst_norm_le _) (productPointEquiv_snd_norm_le _)

lemma productPointEquiv_symm_norm_le (d e : ℕ) (p : Point d × Point e) :
    ‖(productPointEquiv d e).symm p‖≤2*‖p‖ := by
  have h := productPointEquiv_norm_sq ((productPointEquiv d e).symm p)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  have h1 : ‖p.1‖≤‖p‖ := norm_fst_le p
  have h2 : ‖p.2‖≤‖p‖ := norm_snd_le p
  have h1' := pow_le_pow_left₀ (norm_nonneg p.1) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg p.2) h2 2
  nlinarith [norm_nonneg p,norm_nonneg ((productPointEquiv d e).symm p)]

lemma productPointEquiv_symm_lipschitz_two (d e : ℕ) :
    LipschitzWith 2 (productPointEquiv d e).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa only [NNReal.coe_ofNat,dist_eq_norm,←map_sub] using
    productPointEquiv_symm_norm_le d e (y-z)

lemma centering_joint_product_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ}
    (hr : 0<r) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    (gibbs (centeringPotential F x r T)).map (productPointEquiv d d)=
      (interpolationLaw F x r T).prod (stdGaussian (Point d)) := by
  rw [centeringPotential,productPotential_gibbs
    (interpolationPotential_smooth hF x hr.le hl hT0 hT1).continuous
    (gaussianPotential_polySmooth d).smooth.continuous,gaussianPotential_gibbs]
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith only [hl])
    (by nlinarith [probability_time hT0 hT1])]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature TensorEnergy RMSIntegral
open scoped Classical BigOperators NNReal

def centeringVelocityJoint {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (y : Point (d+d)) : Point (d+d) :=
  (productPointEquiv d d).symm
    (centeringVelocityPicard F x r T h ψ s n m N e (productPointEquiv d d y))

lemma actual_centering_joint_field {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s : ℝ) (y : Point (d+d)) :
    productPointEquiv d d (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y)=
    skewCenteringField (centeringKernel hF x hr hl hT0 hT1)
      (fun z => conditionalFieldMean F x r T z-primitiveExpectedField F x r) s
      (productPointEquiv d d y) := by
  apply jointSkew_field ((interpolationPotential_smooth hF x hr.le hl hT0 hT1).differentiable (by simp))
  · intro i j
    exact (contDiff_const.inner ℝ
      ((centeringKernel_smooth hF x hr hlam hl hT0 hT1).clm_apply contDiff_const)).differentiable (by simp)
  · exact centeringKernel_strong hF x hr hlam hl hT0 hT1

lemma centeringVelocityJoint_error_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h ψ s : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1)) (y : Point (d+d)) :
    ‖centeringVelocityJoint F x r T h ψ s n m N e y-
      skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2=
    (r*s)⁻¹^2 * ‖kernelQuadraturePicard F x r T h ψ (n+1) m N e
        (terminalQuadratureWeight T h n) (productPointEquiv d d y)-
        r • (centeringKernel hF x hr hl hT0 hT1 (productPointEquiv d d y).1).adjoint
          (productPointEquiv d d y).2‖^2 := by
  rw [productPointEquiv_norm_sq,map_sub,actual_centering_joint_field hF x hr hlam hl hT0 hT1]
  simp only [centeringVelocityJoint,ContinuousLinearEquiv.apply_symm_apply,
    centeringVelocityPicard,skewCenteringField,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero]
  have hscale : -(r*s)⁻¹*r= -s⁻¹ := by field_simp
  rw [←hscale,←smul_smul,←smul_sub,norm_smul,mul_pow]
  simp only [Real.norm_eq_abs,sq_abs,neg_sq]
  ring

lemma centeringVelocityJoint_rms_of_kernel {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h ψ s : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1)) {B : ℝ}
    (hK : Continuous (kernelQuadraturePicard F x r T h ψ (n+1) m N e (terminalQuadratureWeight T h n)))
    (hi : Integrable (fun p => ‖kernelQuadraturePicard F x r T h ψ (n+1) m N e
      (terminalQuadratureWeight T h n) p-r •
      (centeringKernel hF x hr hl hT0 hT1 p.1).adjoint p.2‖^2)
      ((interpolationLaw F x r T).prod (stdGaussian (Point d))))
    (hb : (∫p,‖kernelQuadraturePicard F x r T h ψ (n+1) m N e (terminalQuadratureWeight T h n) p-
      r • (centeringKernel hF x hr hl hT0 hT1 p.1).adjoint p.2‖^2
      ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤B) :
    let err := fun y => centeringVelocityJoint F x r T h ψ s n m N e y-
      skewLieField (centeringPotential F x r T) (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y
    Integrable (fun y => ‖err y‖^2) (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖err y‖^2 ∂gibbs (centeringPotential F x r T))≤(r*s)⁻¹^2*B := by
  intro err
  let f := fun p : Point d × Point d => ‖kernelQuadraturePicard F x r T h ψ (n+1) m N e
      (terminalQuadratureWeight T h n) p-r •(centeringKernel hF x hr hl hT0 hT1 p.1).adjoint p.2‖^2
  have hc : Continuous f := by
    apply Continuous.pow
    apply Continuous.norm
    apply hK.sub
    exact (continuous_const_smul r).comp
      ((ContinuousLinearMap.adjoint.continuous.comp
        ((centeringKernel_smooth hF x hr hlam hl hT0 hT1).continuous.comp continuous_fst)).clm_apply continuous_snd)
  have he := centering_joint_product_law hF x hr hl hT0 hT1
  have hp : Integrable (fun y => f (productPointEquiv d d y)) (gibbs (centeringPotential F x r T)) := by
    apply (integrable_map_measure hc.measurable.aestronglyMeasurable
      (productPointEquiv d d).continuous.measurable.aemeasurable).mp
    rw [he]
    exact hi
  have hb' : (∫y,f (productPointEquiv d d y) ∂gibbs (centeringPotential F x r T))≤B := by
    rw [←integral_map (productPointEquiv d d).continuous.measurable.aemeasurable hc.measurable.aestronglyMeasurable,he]
    exact hb
  dsimp only [err]
  simp_rw [centeringVelocityJoint_error_sq hF x hr hlam hl hT0 hT1]
  refine ⟨hp.const_mul _,?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hb' (sq_nonneg _)
end LogConcaveSampling

end

end

end OAI
