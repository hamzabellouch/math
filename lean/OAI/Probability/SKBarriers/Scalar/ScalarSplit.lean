import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMomentSquare

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchy_translate (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) (c x : ℝ) :
    scalarHierarchy n m v (fun y => f (c+y)) x=scalarHierarchy n m v f (c+x) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [scalarHierarchy]
    rw [funext (scalarStep_translate _ _ c f)]
    exact ih _ _ _

theorem scalarHierarchy_gradient_average (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : ∀ y, HasDerivAt f (g y) y) (x : ℝ) :
    deriv (scalarHierarchy n m v f) x=scalarHierarchyAverage n m v f g x := by
  have he : (fun a => scalarHierarchy n m v (primitivePerturbation f f a) x)=
      fun a => scalarHierarchy n m v f (x+a) := by
    funext a
    have hp : primitivePerturbation f f a=fun y => f (a+y) := by
      funext y
      simp only [primitivePerturbation,add_sub_cancel_left,add_comm y a]
    rw [hp,scalarHierarchy_translate,add_comm a x]
  have hd := ((scalarHierarchy_regular n m v hf).1.differentiable (by norm_num) x).hasDerivAt
  have hd' : HasDerivAt (scalarHierarchy n m v f) (deriv (scalarHierarchy n m v f) x) (x+0) := by simpa only [add_zero] using hd
  have H := hd'.comp 0 ((hasDerivAt_id (0:ℝ)).const_add x)
  simp only [mul_one] at H
  have H' := scalarHierarchy_primitive_derivative n m v hf hf hg x 0
  have Hd : deriv (fun a => scalarHierarchy n m v f (x+a)) 0=deriv (scalarHierarchy n m v f) x := by
    simpa only [Function.comp_def] using H.deriv
  rw [he,Hd,primitivePerturbation_zero] at H'
  simpa only [add_zero] using H'

theorem scalarHierarchy_split (a b : ℕ) (m v : Fin (a+b) → ℝ) (f : ℝ → ℝ) :
    scalarHierarchy (a+b) m v f=
      scalarHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  induction b generalizing f with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)

theorem scalarHierarchyAverage_split (a b : ℕ) (m v : Fin (a+b) → ℝ) (f g : ℝ → ℝ) :
    scalarHierarchyAverage (a+b) m v f g=
      scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (scalarHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g) := by
  induction b generalizing f g with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
      (scalarStepAverage (m (Fin.last (a+b))) (v (Fin.last (a+b))) f g)

theorem scalarMomentSquare_split (a b : ℕ) (m v : Fin (a+b) → ℝ) (f g : ℝ → ℝ) :
    scalarMomentSquare (a+b) m v f g ⟨a, by omega⟩=
      scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (fun x => (scalarHierarchyAverage b (fun i => m (i.natAdd a))
          (fun i => v (i.natAdd a)) f g x)^2) := by
  induction b generalizing f g with
  | zero =>
    cases a with
    | zero => rfl
    | succ a =>
      change scalarMomentSquare (a+1) m v f g (Fin.last (a+1))=_
      rw [scalarMomentSquare,Fin.lastCases_last]
      rfl
  | succ b ih =>
    change scalarMomentSquare (a+b+1) m v f g (Fin.castSucc ⟨a, by omega⟩)=_
    rw [scalarMomentSquare,Fin.lastCases_castSucc]
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
      (scalarStepAverage (m (Fin.last (a+b))) (v (Fin.last (a+b))) f g)

end SK.Analytic

end
end

end OAI
