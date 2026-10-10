import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarJointLoss

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchy_hessian_square_cramer {f : ℝ → ℝ}
    (hf : BoundedDerivs f) (hc : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i,m i∈Icc (0:ℝ) 1) (x : ℝ) :
    (∑ i,(v i)^2)*(rootHessian 0 (scalarHierarchy n m v f) x)^2 ≤
      (1+2*(∑ i,(v i)^2))*(scalarHierarchyAverage n m v f
        (fun y => (rootGradient 0 f y)^2) x-(rootGradient 0 (scalarHierarchy n m v f) x)^2) := by
  let S := ∑ i,(v i)^2
  let K := scalarHierarchyAverage n m v f (rootHessian 0 f) x
  let H := rootHessian 0 (scalarHierarchy n m v f) x
  let V := scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
    (rootGradient 0 (scalarHierarchy n m v f) x)^2
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd := scalarHierarchy_cramer_data hf hc n m v hm x
  change 0≤K ∧ K≤H ∧ H≤K+V ∧ S*K^2≤V at hd

  have hH1 : H≤1 := (le_abs_self H).trans ((hc.scalarHierarchy hf n m v hm).bounds x).2
  have hV : 0≤V := (mul_nonneg hS (sq_nonneg _)).trans hd.2.2.2
  have he : H^2≤K^2+2*V := by
    have hdiff : 0≤H-K := sub_nonneg.mpr hd.2.1
    have hsum : H+K≤2 := by linarith [hd.2.1]
    have hh := mul_le_mul_of_nonneg_left hsum hdiff
    nlinarith [hd.2.2.1]
  have heS := mul_le_mul_of_nonneg_left he hS
  change S*H^2≤(1+2*S)*V
  nlinarith [hd.2.2.2]

theorem scalarIncrementAverage_hessian_square_cramer (l j : List (ℝ × ℝ))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hc : ScalarSpinConvex f)
    (hj : ∀ p∈j,p.1∈Icc (0:ℝ) 1) :
    let H := scalarIncrementChain j f
    rawVariance j*scalarIncrementAverage l H (fun x => (rootHessian 0 H x)^2) 0 ≤
      (1+2*rawVariance j)*(scalarIncrementAverage (l++j) f (fun x => (rootGradient 0 f x)^2) 0-
        scalarIncrementAverage l H (fun x => (rootGradient 0 H x)^2) 0) := by
  dsimp only
  let H := scalarIncrementChain j f
  have hH := scalarIncrementChain_regular j hf
  have hHc : ScalarSpinConvex H := by
    change ScalarSpinConvex (scalarIncrementChain j f)
    rw [scalarIncrementChain_get]
    exact hc.scalarHierarchy hf _ _ _ (fun i => hj _ (List.get_mem _ _))
  have hχ := hHc.hessian_bounded hH
  have hU := hHc.gradient_bounded hH
  have hV := (scalarIncrementAverage_bounded j hf (hc.gradient_bounded hf).sq).sub hU.sq
  have hpoint (x : ℝ) : rawVariance j*(rootHessian 0 H x)^2 ≤
      (1+2*rawVariance j)*(scalarIncrementAverage j f (fun y => (rootGradient 0 f y)^2) x-
        (rootGradient 0 H x)^2) := by
    have G := scalarHierarchy_hessian_square_cramer hf hc j.length
      (fun i => (j.get i).1) (fun i => (j.get i).2) (fun i => hj _ (List.get_mem _ _)) x
    rw [sum_get_map j (fun p => p.2^2)] at G
    simpa only [H,scalarIncrementChain_get,scalarIncrementAverage_get,rawVariance] using G
  have G := scalarIncrementAverage_mono l hH (hχ.sq.const_mul (rawVariance j))
    (hV.const_mul (1+2*rawVariance j)) hpoint 0
  change rawVariance j*scalarIncrementAverage l H (fun x => (rootHessian 0 H x)^2) 0 ≤ _
  have hleft := scalarHierarchyAverage_const_mul hH hχ.sq
    (n:=l.length) (m:=fun i => (l.get i).1) (v:=fun i => (l.get i).2)
    (c:=rawVariance j) (x:=0)
  have hright := scalarHierarchyAverage_const_mul hH hV
    (n:=l.length) (m:=fun i => (l.get i).1) (v:=fun i => (l.get i).2)
    (c:=1+2*rawVariance j) (x:=0)
  have hsub := scalarHierarchyAverage_sub hH
    (scalarIncrementAverage_bounded j hf (hc.gradient_bounded hf).sq) hU.sq
    (n:=l.length) (m:=fun i => (l.get i).1) (v:=fun i => (l.get i).2) (x:=0)
  simp only [← scalarIncrementAverage_get] at hleft hright hsub
  rw [hleft,hright] at G
  change rawVariance j*scalarIncrementAverage l H (fun x => (rootHessian 0 H x)^2) 0 ≤
    (1+2*rawVariance j)*scalarIncrementAverage l H (fun x => scalarIncrementAverage j f
      (fun y => (rootGradient 0 f y)^2) x-(rootGradient 0 H x)^2) 0 at G
  rw [hsub] at G
  rw [scalarIncrementAverage_append]
  exact G

end SK.Analytic

end
end

end OAI
