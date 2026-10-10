import OAI.Geometry.Relativity.CKS.BondiBalance
import OAI.Geometry.Relativity.CKS.TailConstraints

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRound CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

def constructedTensor (f₀ : C(Sphere,ℝ)) (m R : ℝ) : Point → CKSRound.Mat :=
  outerTensor (outerMass f₀ m R) (bendingV R) (bendingBeta R) (outerA f₀ R) (outerPhi f₀ R)

def constructedTensorJet (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : Point) : TensorJet :=
  tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
    (radial (normalEntry (bendingV R) (bendingBeta R)))
    (correctedComponent (bendingV R) (outerA f₀ R))
    (correctedComponent (bendingV R) (outerPhi f₀ R)) x

lemma constructedTensor_tail (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : Point} (hr : 2*R^2 < x 0) : constructedTensor f₀ m R x = 0 := by
  have hRp : 0 < R := by linarith
  have hv := bendingV_tail hRp hr.le
  have hvp := bendingV_tail_deriv hRp hr
  have hb := bendingBeta_tail hR hr.le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [constructedTensor,outerTensor,tensor,radial,normalEntry,correctedComponent,correctionCoeff,hv,hvp,hb]

lemma constructedTensorJet_tail (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : Point} (hr : 2*R^2 < x 0) :
    constructedTensorJet f₀ m R x = {val := 0, d := 0} := by
  have hn : constructedTensor f₀ m R =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(coord 0).continuous.continuousAt.eventually (eventually_gt_nhds hr)] with y hy
    exact constructedTensor_tail f₀ m hR hy
  change TensorJet.mk _ _ = TensorJet.mk _ _
  apply congrArg₂ TensorJet.mk
  · exact constructedTensor_tail f₀ m hR hr
  · funext d i j
    change D (basis d) (fun y => constructedTensor f₀ m R y i j) x = 0
    have he : (fun y => constructedTensor f₀ m R y i j) =ᶠ[𝓝 x] (fun _ => 0) :=
      hn.mono (fun y hy => congrFun (congrFun hy i) j)
    rw [D_congr he,D_const]

theorem constructed_momentum_tail (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : Point} (hr : 2*R^2 < x 0) (i : Idx) :
    (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x).momentum
      (constructedTensorJet f₀ m R x) i = 0 := by
  rw [constructedTensorJet_tail f₀ m hR hr]
  simp [MetricJet.momentum,MetricJet.tensorDivergence,MetricJet.dTrace]

end
end CKSSphericalChart

end

end OAI
