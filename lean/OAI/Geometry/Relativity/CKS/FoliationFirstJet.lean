import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.FoliationReconstruction

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus
open scoped BigOperators
 def foliationMetricDerivative (U : ℝ) (γ : Mat) (s : Point)
    (dU : ℝ) (dγ : Mat) (ds : Point) : AmbientMat :=
  metricBlock (-2*dU/U^3+∑ a, ∑ b,
    (dγ a b*s a*s b+γ a b*ds a*s b+γ a b*s a*ds b))
    (fun a => ∑ b, (dγ a b*s b+γ a b*ds b)) dγ

 def foliationNormalDerivative (U : ℝ) (s : Point) (dU : ℝ) (ds : Point) : PhysicalPoint :=
  ![dU,-dU*s 0-U*ds 0,-dU*s 1-U*ds 1]

lemma foliationMetric_derivative (e : PhysicalPoint) {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : U x ≠ 0) :
    (fun i j => D e (fun y => foliationMetric (U y) (γ y) (s y) i j) x) =
      foliationMetricDerivative (U x) (γ x) (s x) (D e U x)
        (fun i j => D e (fun y => γ y i j) x) (fun i => D e (fun y => s y i) x) := by
  have hγc (i j) : DifferentiableAt ℝ (fun y => γ y i j) x := differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have dsum (f : Fin 2 → PhysicalPoint → ℝ)
      (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
      D e (fun y => ∑ i, f i y) x = ∑ i, D e (f i) x := by
    simp only [D, fderiv_fun_sum (fun i _ => hf i), _root_.sum_apply]
  have hUi2 : DifferentiableAt ℝ (fun y => 1/(U y)^2) x :=
    CKSCalculus.diffAt_div (differentiableAt_const 1) (hU.pow 2) (pow_ne_zero _ h0)
  have ht (a b : Fin 2) : DifferentiableAt ℝ (fun y => γ y a b*s y a*s y b) x :=
    ((hγc a b).fun_mul (hsc a)).fun_mul (hsc b)
  have hsum (a : Fin 2) : DifferentiableAt ℝ (fun y => ∑ b, γ y a b*s y a*s y b) x :=
    DifferentiableAt.fun_sum (fun b _ => ht a b)
  have hrr : D e (fun y => 1/(U y)^2+∑ a, ∑ b, γ y a b*s y a*s y b) x =
      -2*D e U x/(U x)^3+∑ a, ∑ b,
        (D e (fun y => γ y a b) x*s x a*s x b+
          γ x a b*D e (fun y => s y a) x*s x b+
          γ x a b*s x a*D e (fun y => s y b) x) := by
    rw [D_add e hUi2 (DifferentiableAt.fun_sum (fun a _ => hsum a)),
      D_inv_sq e hU h0, dsum _ hsum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [dsum _ (ht a)]
    apply Finset.sum_congr rfl
    intro b _
    rw [D_mul e ((hγc a b).fun_mul (hsc a)) (hsc b), D_mul e (hγc a b) (hsc a)]
    ring
  have hmixed (a : Fin 2) : D e (fun y => ∑ b, γ y a b*s y b) x =
      ∑ b, (D e (fun y => γ y a b) x*s x b + γ x a b*D e (fun y => s y b) x) := by
    rw [dsum _ (fun b => (hγc a b).fun_mul (hsc b))]
    apply Finset.sum_congr rfl
    intro b _
    rw [D_mul e (hγc a b) (hsc b)]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hmixed 0
  · exact hmixed 1
  · exact hmixed 0
  · rfl
  · rfl
  · exact hmixed 1
  · rfl
  · rfl

lemma foliationNormal_derivative (e : PhysicalPoint) {U : PhysicalPoint → ℝ}
    {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hs : DifferentiableAt ℝ s x) :
    (fun i => D e (fun y => foliationNormal (U y) (s y) i) x)=
      foliationNormalDerivative (U x) (s x) (D e U x) (fun i => D e (fun y => s y i) x) := by
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  ext i
  fin_cases i <;> dsimp [foliationNormal,foliationNormalDerivative]
  all_goals rw [D_mul (f := fun y => -U y) e hU.neg (hsc _)]
  all_goals simp only [D, fderiv_fun_neg, _root_.neg_apply]
  all_goals ring

end
end CKSAngularGeometry

end

end OAI
