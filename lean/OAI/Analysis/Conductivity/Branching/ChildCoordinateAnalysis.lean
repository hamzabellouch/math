import Mathlib
import OAI.Analysis.Conductivity.Branching.CentralChildCollar
import OAI.Analysis.Conductivity.Fourier.AngularIntegratedTrace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def sourceChildHomeomorph (σ : ℝ) : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) where
  toFun := sourceChildCoordinates σ
  invFun := fun z => ![z 1/sourceScale,(z 0-σ*sourceOffset)/sourceScale,z 2/sourceScale]
  left_inv := by intro x; ext i; fin_cases i <;> simp [sourceChildCoordinates,sourceScale]
  right_inv := by intro x; ext i; fin_cases i <;> simp [sourceChildCoordinates,sourceScale] <;> ring
  continuous_toFun := by apply continuous_pi; intro i; fin_cases i <;> dsimp [sourceChildCoordinates] <;> fun_prop
  continuous_invFun := by apply continuous_pi; intro i; fin_cases i <;> dsimp <;> fun_prop

def sourceChildJacobian : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0,sourceScale,0],![sourceScale,0,0],![0,0,sourceScale]]

def sourceChildDerivative : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin' sourceChildJacobian).toContinuousLinearMap

lemma sourceChildDerivative_apply (x : Fin 3 → ℝ) :
    sourceChildDerivative x=![sourceScale*x 1,sourceScale*x 0,sourceScale*x 2] := by
  ext i; fin_cases i <;> simp [sourceChildDerivative,sourceChildJacobian,Matrix.toLin',LinearMap.toMatrix',Matrix.mulVecLin,
    Matrix.mulVecBilin,Matrix.mulVec,Fin.sum_univ_succ,dotProduct]

lemma sourceChildCoordinates_contDiff (σ : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceChildCoordinates σ) := by
  apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp [sourceChildCoordinates] <;> fun_prop

lemma sourceChildCoordinates_hasFDeriv (σ : ℝ) (x : Fin 3 → ℝ) :
    HasFDerivAt (sourceChildCoordinates σ) sourceChildDerivative x := by
  have he : sourceChildCoordinates σ=fun y => sourceChildDerivative y+![σ*sourceOffset,0,0] := by
    funext y; rw [sourceChildDerivative_apply]; ext i; fin_cases i <;> simp [sourceChildCoordinates]
  rw [he]
  simpa using sourceChildDerivative.hasFDerivAt.add_const ![σ*sourceOffset,0,0]

lemma sourceChildDerivative_det : sourceChildDerivative.det= -sourceScale^3 := by
  change (Matrix.toLin' sourceChildJacobian).det= -sourceScale^3
  rw [LinearMap.det_toLin',Matrix.det_fin_three]
  simp [sourceChildJacobian]
  ring

lemma sourceChildDerivative_norm : ‖sourceChildDerivative‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [sourceChildDerivative_apply,one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  have h0 := norm_le_pi_norm x (0 : Fin 3)
  have h1 := norm_le_pi_norm x (1 : Fin 3)
  have h2 := norm_le_pi_norm x (2 : Fin 3)
  simp only [Real.norm_eq_abs] at h0 h1 h2
  fin_cases i <;> simp only [Fin.isValue,
    Real.norm_eq_abs] <;> norm_num [sourceScale] <;> nlinarith [abs_nonneg (x 0),abs_nonneg (x 1),abs_nonneg (x 2)]

lemma sourceChild_energy {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (σ : ℝ) (x : Fin 3 → ℝ) :
    sourcePhysicalEnergy (f ∘ sourceChildCoordinates σ) x≤ sourcePhysicalEnergy f (sourceChildCoordinates σ x) := by
  have he := ((hf.differentiable (by simp) _).hasFDerivAt.comp x (sourceChildCoordinates_hasFDeriv σ x)).fderiv
  have hn := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ f (sourceChildCoordinates σ x)) sourceChildDerivative
  have hl := hn.trans (mul_le_of_le_one_right (norm_nonneg _) sourceChildDerivative_norm)
  have hs := mul_self_le_mul_self (norm_nonneg _) hl
  dsimp only [sourcePhysicalEnergy,Function.comp_apply]
  rw [he]
  nlinarith

lemma integral_sourceChild_preimage (σ : ℝ) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (g : (Fin 3 → ℝ) → ℝ) :
    (∫ x in sourceChildCoordinates σ ⁻¹' K,g (sourceChildCoordinates σ x))=
      (sourceScale^3)⁻¹*(∫ y in K,g y) := by
  have hs : sourceScale≠0 := by norm_num [sourceScale]
  have hc := (sourceChildHomeomorph σ).isCompact_preimage.mpr hK
  have hh := integral_image_eq_integral_abs_det_fderiv_smul volume hc.measurableSet
    (fun x _ => (sourceChildCoordinates_hasFDeriv σ x).hasFDerivWithinAt)
    (sourceChildHomeomorph σ).injective.injOn g
  have him : sourceChildCoordinates σ '' (sourceChildCoordinates σ ⁻¹' K)=K :=
    Set.image_preimage_eq K (sourceChildHomeomorph σ).surjective
  change (∫ x in sourceChildCoordinates σ '' (sourceChildCoordinates σ ⁻¹' K),g x)=
    ∫ x in sourceChildCoordinates σ ⁻¹' K,abs sourceChildDerivative.det • g (sourceChildCoordinates σ x) at hh
  rw [him] at hh
  simp only [sourceChildDerivative_det,abs_neg,abs_pow,abs_of_nonneg (show 0≤sourceScale by norm_num [sourceScale]),
    smul_eq_mul,integral_const_mul] at hh
  norm_num [sourceScale] at hh ⊢
  linarith

end ScalarConductivity

end

end OAI
