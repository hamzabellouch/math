import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1Pairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGreenAlgebra
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyCoordinates

namespace OAI

/-! The intrinsic tangent inner product is the literal three-coordinate
sesquilinear sum. This fixes the local normalization of the weak form. -/
noncomputable section
open scoped Matrix
namespace CubicFirstMoment

lemma cubicThetaLinear_inner_of_norm_eq
    {V E G : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (L : V →ₗ[ℂ] E) (M : V →ₗ[ℂ] G) (h : ∀ v, ‖L v‖=‖M v‖) (v w : V) :
    inner ℂ (L v) (L w)=inner ℂ (M v) (M w) := by
  rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four]
  simp only [← map_add,← map_sub,← map_smul]
  simp only [h]

def cubicThetaTangentValues : ((ℂ × ℝ) →L[ℝ] ℂ) →ₗ[ℂ] CubicThetaGradient where
  toFun L := WithLp.toLp 2 (fun i => L (cubicThetaTangentCoordinates (cubicThetaTangentBasis i)))
  map_add' L M := by ext i; rfl
  map_smul' c L := by ext i; rfl

def cubicThetaCoordinateValues : ((ℂ × ℝ) →L[ℝ] ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun L := WithLp.toLp 2 ![L (1,0),L (Complex.I,0),L (0,1)]
  map_add' L M := by ext i; fin_cases i <;> rfl
  map_smul' c L := by ext i; fin_cases i <;> rfl

lemma cubicThetaTangentValues_norm (L : (ℂ × ℝ) →L[ℝ] ℂ) :
    ‖cubicThetaTangentValues L‖=‖cubicThetaCoordinateValues L‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  change cubicThetaTangentEnergy (L.comp cubicThetaTangentCoordinates.toContinuousLinearMap)=_
  rw [cubicThetaTangentEnergy_coordinates]
  simp [cubicThetaCoordinateValues,Fin.sum_univ_succ,add_assoc]

lemma cubicThetaTangentValues_inner (L M : (ℂ × ℝ) →L[ℝ] ℂ) :
    inner ℂ (cubicThetaTangentValues L) (cubicThetaTangentValues M)=
      star (L (1,0))*M (1,0)+star (L (Complex.I,0))*M (Complex.I,0)+
        star (L (0,1))*M (0,1) := by
  rw [cubicThetaLinear_inner_of_norm_eq cubicThetaTangentValues cubicThetaCoordinateValues
    cubicThetaTangentValues_norm]
  simp [cubicThetaCoordinateValues,PiLp.inner_apply,Fin.sum_univ_succ,RCLike.inner_apply,mul_comm,add_assoc]

lemma cubicThetaSectionGradient_pair_coordinates (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (p : CubicThetaPoint) :
    inner ℂ (cubicThetaSectionGradient F p) (cubicThetaSectionGradient G p)=
      (p.val.2:ℂ)^2*cubicThetaCoordinatePairing (cubicThetaSectionFunction F)
        (cubicThetaSectionFunction G) p.val := by
  have hp : {y : ℂ × ℝ | 0<y.2}∈nhds p.val :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds p.property
  have hf := (hF.contDiffAt hp).differentiableAt (by norm_num)
  have hg := (hG.contDiffAt hp).differentiableAt (by norm_num)
  have heF : cubicThetaSectionGradient F p=(p.val.2:ℂ) •
      cubicThetaTangentValues (fderiv ℝ (cubicThetaSectionFunction F) p.val) := by
    ext i
    simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,cubicThetaTangentValues,
      ContinuousLinearMap.comp_apply]
    rfl
  have heG : cubicThetaSectionGradient G p=(p.val.2:ℂ) •
      cubicThetaTangentValues (fderiv ℝ (cubicThetaSectionFunction G) p.val) := by
    ext i
    simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,cubicThetaTangentValues,
      ContinuousLinearMap.comp_apply]
    rfl
  rw [heF,heG,inner_smul_left,inner_smul_right,cubicThetaTangentValues_inner]
  unfold cubicThetaCoordinatePairing
  simp only [cubicThetaAxisFirst_eq_fderiv _ _ hf,cubicThetaAxisFirst_eq_fderiv _ _ hg,
    cubicThetaAxisVector]
  have hs : (starRingEnd ℂ) (p.val.2:ℂ)=(p.val.2:ℂ) := by simp
  rw [hs]
  ring

end CubicFirstMoment

end

end OAI
