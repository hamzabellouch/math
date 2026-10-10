import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiConnection
import OAI.Geometry.PrescribedPotential.MetricQuasilinearEquation
import OAI.Geometry.PrescribedPotential.PrincipalComponents
import OAI.Geometry.PrescribedPotential.QuasilinearJetBasics

namespace OAI

/-! Encoded Metric Equation. -/

section

noncomputable section
open Set Filter Topology Matrix Finset
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace MetricSystem
open EllipticKernel FrozenPoisson HigherJet KaehlerCalculus
variable {n : ℕ}
local instance equationRealHMIP : InnerProductSpace ℝ (HM n) := InnerProductSpace.rclikeToReal ℂ (HM n)
local instance equationRealECIP : InnerProductSpace ℝ (EC n) := InnerProductSpace.rclikeToReal ℂ (EC n)

lemma encoded_W {M : V n → Mat n} {z : V n} (hM : ContDiffAt ℝ ∞ M z)
    (a : ℂ) (v : V n) :
    W a v (fderiv ℝ (fun x => encode n (M (coordinateEquiv n x))) ((coordinateEquiv n).symm z)) =
      mderiv a v M z := by
  have hd := ((encode n).hasFDerivAt.comp ((coordinateEquiv n).symm z)
    (((by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hM :
      ContDiffAt ℝ ∞ M (coordinateEquiv n ((coordinateEquiv n).symm z))).differentiableAt (by simp)).hasFDerivAt.comp
      ((coordinateEquiv n).symm z) (coordinateEquiv n).hasFDerivAt))
  have hd' := hd.fderiv
  simp only [Function.comp_def] at hd'
  have hw := congrArg (W a v) hd'
  calc
    _ = _ := hw
    _ = _ := by
      rw [mderiv_eq hM]
      simp only [W,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
      change (1/2:ℂ) • ((encode n).symm (encode n ((fderiv ℝ M z) v))+a • (encode n).symm (encode n ((fderiv ℝ M z) (Complex.I • v)))) = _
      rw [ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearEquiv.symm_apply_apply]

lemma encoded_quadratic {M : V n → Mat n} {z : V n} (hM : ContDiffAt ℝ ∞ M z) :
    quadraticCoefficient (encode n (M z), fderiv ℝ (fun y => encode n (M (coordinateEquiv n y))) ((coordinateEquiv n).symm z)) =
      encode n (∑ i, ∑ j, (M z)⁻¹ i j • (mderiv Complex.I (e j) M z*(M z)⁻¹*mderiv (-Complex.I) (e i) M z)) := by
  unfold quadraticCoefficient
  simp only [inverseCoefficient,ContinuousLinearEquiv.symm_apply_apply]
  apply congrArg (encode n)
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [encoded_W hM,encoded_W hM]

local instance equationHessianNorm : NormedAddCommGroup (EC n →L[ℝ] EC n →L[ℝ] HM n) := inferInstance
local instance equationHessianSpace : NormedSpace ℝ (EC n →L[ℝ] EC n →L[ℝ] HM n) := inferInstance

lemma encoded_metric_equation {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ (EC n))
    (K : LocalKaehlerField n) {x : EC n} (hx : coordinateEquiv n x ∈ K.domain) :
    principalBilinear basis (inverseCoefficient (encode n (K.matrix (coordinateEquiv n x))))
      (hessian (fun y => encode n (K.matrix (coordinateEquiv n y))) x) =
      encode n (K.ricciHessian (coordinateEquiv n x))+
      quadraticCoefficient (firstJet (fun y => encode n (K.matrix (coordinateEquiv n y))) x) := by
  have hK := K.smooth.contDiffAt (K.isOpen.mem_nhds hx)
  have he := encoded_principal basis hK (K.positive _ hx)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at he
  have hQ := encoded_quadratic hK
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hQ
  change principalBilinear basis (K.matrix (coordinateEquiv n x))⁻¹
    (fderiv ℝ (fderiv ℝ (fun y => encode n (K.matrix (coordinateEquiv n y)))) x) = _
  rw [he,K.metric_quasilinear_equation hx,map_add]
  exact congrArg (fun y => encode n (K.ricciHessian (coordinateEquiv n x))+y) hQ.symm
end MetricSystem

end
end

end OAI
