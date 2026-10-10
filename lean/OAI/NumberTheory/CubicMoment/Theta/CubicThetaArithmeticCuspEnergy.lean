import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighCuspDifferentiation

namespace OAI

/-! Exact transport of the arithmetic energy to a cusp, followed by
the operator-norm bound for its genuine joint derivative. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaTangentCoordinates_norm_le (u : CubicThetaTangent) :
    ‖cubicThetaTangentCoordinates u‖≤‖u‖ := by
  rw [Prod.norm_def]
  exact max_le (WithLp.norm_fst_le ℂ u) (WithLp.norm_snd_le ℂ u)

lemma cubicThetaTangentEnergy_coordinate_bound (L : (ℂ × ℝ) →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (L.comp cubicThetaTangentCoordinates.toContinuousLinearMap)≤
      (Module.finrank ℝ CubicThetaTangent:ℝ)*‖L‖^2 := by
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ CubicThetaTangent), ‖L‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := L.le_opNorm (cubicThetaTangentCoordinates (cubicThetaTangentBasis i))
      have hu := cubicThetaTangentCoordinates_norm_le (cubicThetaTangentBasis i)
      rw [cubicThetaTangentBasis.norm_eq_one] at hu
      have hb : ‖L (cubicThetaTangentCoordinates (cubicThetaTangentBasis i))‖≤‖L‖ :=
        h.trans ((mul_le_mul_of_nonneg_left hu (_root_.norm_nonneg L)).trans_eq (mul_one _))
      exact (sq_le_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mpr hb
    _ = _ := by simp

lemma cubicThetaArithmeticCusp_energy_eq (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 2<s.re)
    (p : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (δ • p)=
      p.val.2^2*cubicThetaTangentEnergy
        ((fderiv ℝ (fun q => cubicThetaArithmeticRemainder
          (cubicThetaMobius (cubicThetaFullComplex δ) q) s) p.val).comp
          cubicThetaTangentCoordinates.toContinuousLinearMap) := by
  let F := cubicThetaArithmeticSection s hs
  let g := cubicThetaFullComplex δ
  have hgp := cubicThetaMobius_height_pos g p.property
  have hF := ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hgp)).differentiableAt (by norm_num)
  have hg := (cubicThetaMobius_contDiffAt g p.property).differentiableAt (by simp)
  have he : (fun q => cubicThetaSectionFunction F (cubicThetaMobius g q))=ᶠ[𝓝 p.val]
      (fun q => cubicThetaArithmeticRemainder (cubicThetaMobius g q) s) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds p.property] with q hq
    rw [cubicThetaSectionFunction_apply F (cubicThetaMobius_height_pos g hq)]
    rfl
  have hd := he.fderiv_eq (𝕜:=ℝ)
  have hcomp : fderiv ℝ (fun q => cubicThetaSectionFunction F (cubicThetaMobius g q)) p.val=
      (fderiv ℝ (cubicThetaSectionFunction F) (cubicThetaMobius g p.val)).comp
        (fderiv ℝ (cubicThetaMobius g) p.val) := by
    simpa only [Function.comp_def] using (fderiv_comp p.val hF hg)
  rw [hcomp] at hd
  have ht : (fderiv ℝ (fun q => cubicThetaArithmeticRemainder (cubicThetaMobius g q) s) p.val).comp
      cubicThetaTangentCoordinates.toContinuousLinearMap=
      (cubicThetaSectionDifferential F (δ • p)).comp (cubicThetaTangentDerivative g p.val) := by
    rw [← hd]
    apply ContinuousLinearMap.ext
    intro u
    simp only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,
      cubicThetaFullPointAction_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [ht,cubicThetaTangentEnergy_derivative _ _ p.property]
  change _=p.val.2^2*(((cubicThetaMobius g p.val).2/p.val.2)^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential F (δ • p)))
  unfold cubicThetaSectionEnergy
  rw [cubicThetaFullPointAction_apply]
  field_simp [p.property.ne']
  rfl

lemma cubicThetaArithmeticCusp_energy_le (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 2<s.re)
    (p : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (δ • p)≤
      (Module.finrank ℝ CubicThetaTangent:ℝ)*p.val.2^2*
        ‖fderiv ℝ (fun q => cubicThetaArithmeticRemainder
          (cubicThetaMobius (cubicThetaFullComplex δ) q) s) p.val‖^2 := by
  rw [cubicThetaArithmeticCusp_energy_eq δ hs p]
  exact (mul_le_mul_of_nonneg_left (cubicThetaTangentEnergy_coordinate_bound _) (sq_nonneg _)).trans_eq
    (by ring)

end CubicFirstMoment

end

end OAI
