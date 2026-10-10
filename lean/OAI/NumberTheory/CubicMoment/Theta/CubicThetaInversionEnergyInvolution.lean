import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionInvolutive
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWeakUniqueness
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinatePairing

namespace OAI

/-! Inversion is an involutive isometry of the actual energy space and
preserves its mass form. It therefore preserves every spectral kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFullInversion_involutive (p : CubicThetaPoint) :
    cubicThetaFullInversion • (cubicThetaFullInversion • p)=p := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion)
    (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val)=p.val
  rw [cubicThetaFullInversion_complex,
    cubicThetaMobius_inversion one_ne_zero (cubicThetaMobius_height_pos _ p.property),
    cubicThetaMobius_inversion one_ne_zero p.property]
  exact cubicThetaInversion_involutive one_ne_zero p.property

lemma cubicThetaInversionSection_involutive (F : CubicThetaSection) :
    cubicThetaInversionSection (cubicThetaInversionSection F)=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  change F.val (cubicThetaFullInversion • (cubicThetaFullInversion • p))=F.val p
  rw [cubicThetaFullInversion_involutive]

lemma cubicThetaInversionSmooth_involutive (F : cubicThetaSmoothTests) :
    cubicThetaInversionSmooth (cubicThetaInversionSmooth F)=F := by
  apply Subtype.ext
  exact cubicThetaInversionSection_involutive F

theorem cubicThetaInversionEnergy_involutive (u : cubicThetaGlobalEnergySpace) :
    cubicThetaInversionEnergy (cubicThetaInversionEnergy u)=u := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq (cubicThetaInversionEnergy.continuous.comp
      cubicThetaInversionEnergy.continuous) continuous_id) ?_
  intro F
  change cubicThetaInversionEnergy (cubicThetaInversionEnergy
    (cubicThetaGlobalEnergyTest F))=cubicThetaGlobalEnergyTest F
  rw [cubicThetaInversionEnergy_test,cubicThetaInversionEnergy_test,
    cubicThetaInversionSmooth_involutive]

lemma cubicThetaInversionEnergy_mass_norm (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaGlobalInclusion (cubicThetaInversionEnergy u)‖=
      ‖cubicThetaGlobalInclusion u‖ := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq (cubicThetaGlobalInclusion.continuous.comp
      cubicThetaInversionEnergy.continuous).norm cubicThetaGlobalInclusion.continuous.norm) ?_
  intro F
  change ‖cubicThetaGlobalInclusion (cubicThetaInversionEnergy
    (cubicThetaGlobalEnergyTest F))‖=‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖
  rw [cubicThetaInversionEnergy_test]
  exact (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
    (cubicThetaInversion_test_mass_norm F)

lemma cubicThetaInversionEnergy_mass_inner (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaInversionEnergy u))
      (cubicThetaGlobalInclusion (cubicThetaInversionEnergy v))=
        inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion v) := by
  exact cubicThetaLinear_inner_of_norm_eq
    (cubicThetaGlobalInclusion.toLinearMap.comp cubicThetaInversionEnergy.toLinearMap)
    cubicThetaGlobalInclusion.toLinearMap cubicThetaInversionEnergy_mass_norm u v

lemma cubicThetaInversionEnergy_pencil_inner (z : ℂ) (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaInversionEnergy u)
      (cubicThetaEnergyPencil z (cubicThetaInversionEnergy v))=
        inner ℂ u (cubicThetaEnergyPencil z v) := by
  have hf (a b : cubicThetaGlobalEnergySpace) :
      inner ℂ a (cubicThetaEnergyPencil z b)=inner ℂ a b-
        z*inner ℂ (cubicThetaGlobalInclusion a) (cubicThetaGlobalInclusion b) := by
    change inner ℂ a (b-z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion b))=_
    rw [inner_sub_right,inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace)]
    exact congrArg (fun t : ℂ => inner ℂ a b-z*t)
      (cubicThetaGlobalInclusion.adjoint_inner_right a (cubicThetaGlobalInclusion b))
  rw [hf,hf,cubicThetaInversionEnergy.inner_map_map,cubicThetaInversionEnergy_mass_inner]

theorem cubicThetaInversionEnergy_kernel (z : ℂ) (u : cubicThetaGlobalEnergySpace)
    (hu : cubicThetaEnergyPencil z u=0) :
    cubicThetaEnergyPencil z (cubicThetaInversionEnergy u)=0 := by
  apply ext_inner_left ℂ
  intro v
  have h := cubicThetaInversionEnergy_pencil_inner z (cubicThetaInversionEnergy v) u
  rw [cubicThetaInversionEnergy_involutive,hu,inner_zero_right] at h
  exact h.trans (inner_zero_right v).symm

end CubicFirstMoment

end

end OAI
