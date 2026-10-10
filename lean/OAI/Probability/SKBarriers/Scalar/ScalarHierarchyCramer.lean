import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyAverageAlgebra

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem ScalarSpinConvex.scalarHierarchy {f : ℝ → ℝ} (h : ScalarSpinConvex f)
    (hf : BoundedDerivs f) (n : ℕ) (m v : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) :
    ScalarSpinConvex (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact h
  | succ n ih => exact ih (h.scalarStep hf (hm _) _) (scalarStep_regular hf _ _) _ _ (fun i => hm _)

theorem scalarHierarchy_cramer_data {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (x : ℝ) :
    let K := scalarHierarchyAverage n m v f (rootHessian 0 f) x
    let V := scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
      (rootGradient 0 (scalarHierarchy n m v f) x)^2
    let H := rootHessian 0 (scalarHierarchy n m v f) x
    0 ≤ K ∧ K ≤ H ∧ H ≤ K+V ∧ (∑ i, (v i)^2)*K^2 ≤ V := by
  induction n generalizing f with
  | zero => simpa only [scalarHierarchyAverage,scalarHierarchy,Finset.univ_eq_empty,
      Finset.sum_empty,zero_mul,sub_self,add_zero,le_refl,and_true] using (h x).1
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
    have hk0 (y : ℝ) : 0 ≤ k y := integral_nonneg (fun z => (h _).1)
    have hA : 0 ≤ A := scalarHierarchyAverage_nonneg hF hk hk0 n m' v' x
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
    have hbcr : w^2*A^2 ≤ B := by
      have H := scalarHierarchyAverage_mono hF (hk.sq.const_mul (w^2)) hb
        (fun y => scalarStepAverage_cramer hf h (hm _).1 w y) n m' v' x
      rw [scalarHierarchyAverage_const_mul hF hk.sq] at H
      have HJ := scalarHierarchyAverage_sq hF hk n m' v' x
      exact (mul_le_mul_of_nonneg_left HJ (sq_nonneg w)).trans H
    have I := ih hF hFc m' v' (fun i => hm _)
    change 0 ≤ E (rootHessian 0 F) ∧
      E (rootHessian 0 F) ≤ rootHessian 0 (scalarHierarchy n m' v' F) x ∧
      rootHessian 0 (scalarHierarchy n m' v' F) x ≤ E (rootHessian 0 F)+W ∧
      (∑ i, (v' i)^2)*(E (rootHessian 0 F))^2 ≤ W at I
    rw [hEK] at I
    change 0 ≤ A ∧ A ≤ rootHessian 0 (scalarHierarchy n m' v' F) x ∧
      rootHessian 0 (scalarHierarchy n m' v' F) x ≤ A+
        (E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
          (rootGradient 0 (scalarHierarchy n m' v' F) x)^2) ∧
      (∑ i, (v i)^2)*A^2 ≤ E (scalarStepAverage c w f (fun y => (rootGradient 0 f y)^2))-
          (rootGradient 0 (scalarHierarchy n m' v' F) x)^2
    rw [hEV,Fin.sum_univ_castSucc]
    change 0 ≤ A ∧ A ≤ rootHessian 0 (scalarHierarchy n m' v' F) x ∧
      rootHessian 0 (scalarHierarchy n m' v' F) x ≤ A+(W+B) ∧
      ((∑ i, (v' i)^2)+w^2)*A^2 ≤ W+B
    have hc0 := (hm (Fin.last n)).1
    have hc1 := (hm (Fin.last n)).2
    have hAB : A ≤ A+c*B := by dsimp [c]; nlinarith
    have hs0 : 0 ≤ ∑ i, (v' i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hsq : A^2 ≤ (A+c*B)^2 := pow_le_pow_left₀ hA hAB 2
    have HI := (mul_le_mul_of_nonneg_left hsq hs0).trans I.2.2.2
    refine ⟨hA,hAB.trans I.2.1,?_,?_⟩
    · dsimp [c] at I
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hB]
    · nlinarith

theorem scalarHierarchy_cramer {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : ScalarSpinConvex f) (n : ℕ) (m v : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (x : ℝ) :
    let V := scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
      (rootGradient 0 (scalarHierarchy n m v f) x)^2
    (∑ i, (v i)^2)*(max (rootHessian 0 (scalarHierarchy n m v f) x-V) 0)^2 ≤ V := by
  have H := scalarHierarchy_cramer_data hf h n m v hm x
  dsimp only at H ⊢
  have hmax : max (rootHessian 0 (scalarHierarchy n m v f) x-
      (scalarHierarchyAverage n m v f (fun y => (rootGradient 0 f y)^2) x-
        (rootGradient 0 (scalarHierarchy n m v f) x)^2)) 0 ≤
      scalarHierarchyAverage n m v f (rootHessian 0 f) x := by
    apply max_le
    · linarith [H.2.2.1]
    · exact H.1
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) hmax 2)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans H.2.2.2

end SK.Analytic

end
end

end OAI
