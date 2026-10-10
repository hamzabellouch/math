import Mathlib
import OAI.Analysis.HardSphere.Geometry.SqTwiceSqAbs

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped NNReal

lemma ae_self_gradient_square {κ : Type*} [Fintype κ] {C : ℝ≥0}
    {f : EuclideanSpace ℝ κ→ℝ} (hf : LipschitzWith C f) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ (fun y ↦ f y^2) x ∧
      (∑ p, (fderiv ℝ (fun y ↦ f y^2) x (EuclideanSpace.basisFun κ ℝ p))^2)≤
        (4*(C:ℝ)^2)*f x^2 := by
  filter_upwards [hf.ae_differentiableAt (μ:=volume)] with x hx
  refine ⟨hx.pow 2,?_⟩
  rw [←(EuclideanSpace.basisFun κ ℝ).norm_dual,fderiv_fun_pow 2 hx]
  simp only [Nat.reduceSub,pow_one,nsmul_eq_mul,Nat.cast_ofNat,norm_smul,Real.norm_eq_abs]
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀:=x) hf
  have hsq := (sq_le_sq₀ (norm_nonneg _) C.coe_nonneg).mpr hb
  calc
    _ = (4*f x^2)*‖fderiv ℝ f x‖^2 := by rw [mul_pow,sq_abs]; ring
    _ ≤ (4*f x^2)*(C:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

theorem localCloseSmoothCount_ae_gradient (L : Length) {s : ℝ} (hs : 0<s) (hs1 : s≤1) (v : Torus L) :
    ∀ᵐ x : EuclideanConfiguration ι ∂volume,
      DifferentiableAt ℝ (fun y ↦ localCloseSmoothCount L s v (euclideanProject L y)) x ∧
      (∑ p, (fderiv ℝ (fun y ↦ localCloseSmoothCount L s v (euclideanProject L y)) x
          (EuclideanSpace.basisFun (ι×Fin 3) ℝ p))^2)≤
        (4096/s^2)*localCloseSmoothCount L s v (euclideanProject L x) := by
  have h := ae_self_gradient_square (localCloseRoot_euclidean_lipschitz (ι:=ι) L hs hs1 v)
  simp_rw [localCloseRoot_sq] at h
  have hc : (4:ℝ)*(32/s)^2=4096/s^2 := by ring
  rw [←hc]
  exact h

end HardSphere

end

end OAI
