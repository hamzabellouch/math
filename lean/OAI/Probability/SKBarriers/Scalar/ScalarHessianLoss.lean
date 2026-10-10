import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyCramer

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchy_hessian_loss {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {a : ℝ} (ha : ∀ i, a≤ m i) (x : ℝ) :
    scalarHierarchyAverage n m v f (rootHessian 0 f) x+
      a*(scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
        (rootGradient 0 (scalarHierarchy n m v f) x)^2) ≤
      rootHessian 0 (scalarHierarchy n m v f) x := by
  induction n generalizing f with
  | zero => simp only [scalarHierarchyAverage,scalarHierarchy,sub_self,mul_zero,add_zero,le_refl]
  | succ n ih =>
    let c := m (Fin.last n)
    let w := v (Fin.last n)
    let m' : Fin n → ℝ := fun i => m i.castSucc
    let v' : Fin n → ℝ := fun i => v i.castSucc
    let F := scalarStep c w f
    let E : (ℝ → ℝ) → ℝ := fun g => scalarHierarchyAverage n m' v' F g x
    let k := scalarStepAverage c w f (rootHessian 0 f)
    let u := scalarStepAverage c w f (rootGradient 0 f)
    let b := fun y => scalarStepAverage c w f (fun z => (rootGradient 0 f z)^2) y-(u y)^2
    let A := E k
    let B := E b
    let W := E (fun y => (rootGradient 0 F y)^2)-(rootGradient 0 (scalarHierarchy n m' v' F) x)^2
    have hF : BoundedDerivs F := scalarStep_regular hf _ _
    have hFc : ScalarSpinConvex F := h.scalarStep hf (hm _) _
    have hk : BoundedScalar k := (h.hessian_bounded hf).scalarStepAverage hf _ _
    have hu : BoundedScalar u := (h.gradient_bounded hf).scalarStepAverage hf _ _
    have he2 := (h.gradient_bounded hf).sq.scalarStepAverage hf c w
    have hb : BoundedScalar b := he2.sub hu.sq
    have hb0 (y : ℝ) : 0 ≤ b y := scalarStepAverage_variance_nonneg hf
      (rootGradient_continuous 0 hf) (fun z => (h.bounds z).1) c w y
    have hB : 0 ≤ B := scalarHierarchyAverage_nonneg hF hb hb0 n m' v' x
    have hug : rootGradient 0 F=u := funext (scalarStep_rootGradient hf c w)
    have hχ : rootHessian 0 F=fun y => k y+c*b y := funext (scalarStep_rootHessian hf c w)
    have hEK : E (rootHessian 0 F)=A+c*B := by
      rw [hχ]
      exact (scalarHierarchyAverage_add hF hk (hb.const_mul c) n m' v' x).trans
        (congrArg (A+·) (scalarHierarchyAverage_const_mul hF hb n m' v' x c))
    have hEV : E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
        (rootGradient 0 (scalarHierarchy n m' v' F) x)^2=W+B := by
      have H := scalarHierarchyAverage_sub hF he2 hu.sq n m' v' x
      change B=E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-E (fun y => (u y)^2) at H
      dsimp [W]
      rw [hug]
      linarith
    have I := ih hF hFc m' v' (fun i => hm _) (fun i => ha _)
    change E (rootHessian 0 F)+a*W≤rootHessian 0 (scalarHierarchy n m' v' F) x at I
    rw [hEK] at I
    change A+a*(E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
      (rootGradient 0 (scalarHierarchy n m' v' F) x)^2)≤rootHessian 0 (scalarHierarchy n m' v' F) x
    rw [hEV]
    have hac : a≤c := ha _
    nlinarith [mul_nonneg (sub_nonneg.mpr hac) hB]

theorem scalarHierarchy_hessian_loss_cramer {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {a : ℝ} (ha0 : 0≤a) (ha : ∀ i, a≤ m i) (x : ℝ) :
    scalarHierarchyAverage n m v f (rootHessian 0 f) x+
      a*(∑ i, (v i)^2)*(scalarHierarchyAverage n m v f (rootHessian 0 f) x)^2 ≤
      rootHessian 0 (scalarHierarchy n m v f) x := by
  have H := scalarHierarchy_hessian_loss hf h n m v hm ha x
  have C := (scalarHierarchy_cramer_data hf h n m v hm x).2.2.2
  nlinarith [mul_le_mul_of_nonneg_left C ha0]

end SK.Analytic

end
end

end OAI
