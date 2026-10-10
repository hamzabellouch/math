import Mathlib
import OAI.Probability.SKBarriers.Replicas.MergedBranch
import OAI.Probability.SKBarriers.Replicas.CommonBranch
import OAI.Probability.SKBarriers.Replicas.TripleSchedule

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStep_add_frozen {f : E → ℝ} (hf : BoundedDerivs f)
    (g : E → ℝ) (m : ℝ) (v : E) (hg : ∀ x (t : ℝ), g (x+t • v)=g x) :
    vectorStep m v (fun x => f x+g x)=fun x => vectorStep m v f x+g x := by
  let T : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ+
    (ContinuousLinearMap.snd ℝ E ℝ).smulRight v
  have H := gaussianStep_add_prefix (hf.compCLM T) g m
  simpa only [vectorStep,hg,Function.comp_def,T,add_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd'] using H

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorIncrementChain_pullback (L : E →L[ℝ] F) (l : List (ℝ × E)) (f : F → ℝ) :
    vectorIncrementChain l (f ∘ L)=
      vectorIncrementChain (l.map (fun p => (p.1,L p.2))) f ∘ L := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [vectorIncrementChain,ih,vectorStep_pullback]; rfl
end Vector

theorem vectorIncrementChain_real (l : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    vectorIncrementChain l f=scalarIncrementChain l f := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [vectorIncrementChain,scalarIncrementChain,ih,vectorStep_real]

def tripleCoordinate (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

@[simp] theorem tripleCoordinate_apply (i : Fin 3) (x : Fin 3 → ℝ) : tripleCoordinate i x=x i := rfl

theorem tripleStep_coordinate {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : (Fin 3 → ℝ) → ℝ)
    (m : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) (hg : ∀ x (t : ℝ),g (x+t • v)=g x) :
    vectorStep m v (fun x => f (x i)+g x)=fun x => scalarStep m (v i) f (x i)+g x := by
  have H := vectorStep_add_frozen (hf.compCLM (tripleCoordinate i)) g m v hg
  change vectorStep m v (fun x => (f ∘ tripleCoordinate i) x+g x)=
    (fun x => vectorStep m v (f ∘ tripleCoordinate i) x+g x) at H
  rw [vectorStep_pullback,vectorStep_real] at H
  exact H

theorem tripleStep_axis0 {f g h : ℝ → ℝ} (hf : BoundedDerivs f) (m v : ℝ) :
    vectorStep m ![v,0,0] (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => scalarStep m v f (x 0)+g (x 1)+h (x 2) := by
  have H := tripleStep_coordinate hf (fun x => g (x 1)+h (x 2)) m ![v,0,0] 0
    (by intro x t; simp)
  simpa only [Matrix.cons_val_zero,add_assoc] using H

theorem tripleStep_axis1 {f g h : ℝ → ℝ} (hg : BoundedDerivs g) (m v : ℝ) :
    vectorStep m ![0,v,0] (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => f (x 0)+scalarStep m v g (x 1)+h (x 2) := by
  have H := tripleStep_coordinate hg (fun x => f (x 0)+h (x 2)) m ![0,v,0] 1
    (by intro x t; simp)
  simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,add_comm,add_left_comm,add_assoc] using H

theorem tripleStep_axis2 {f g h : ℝ → ℝ} (hh : BoundedDerivs h) (m v : ℝ) :
    vectorStep m ![0,0,v] (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => f (x 0)+g (x 1)+scalarStep m v h (x 2) := by
  have H := tripleStep_coordinate hh (fun x => f (x 0)+g (x 1)) m ![0,0,v] 2
    (by intro x t; simp)
  simpa [add_comm,add_left_comm,add_assoc] using H

theorem tripleTailBlock_value {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedDerivs g) (hh : BoundedDerivs h) (p : ℝ × ℝ) :
    vectorIncrementChain (tripleTailBlock p) (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => scalarStep p.1 p.2 f (x 0)+scalarStep p.1 p.2 g (x 1)+scalarStep p.1 p.2 h (x 2) := by
  simp only [tripleTailBlock,vectorIncrementChain,tripleStep_axis2 hh,tripleStep_axis1 hg,tripleStep_axis0 hf]

theorem tripleTailSchedule_value {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedDerivs g) (hh : BoundedDerivs h) (l : List (ℝ × ℝ)) :
    vectorIncrementChain (tripleTailSchedule l) (fun x : Fin 3 → ℝ => f (x 0)+g (x 1)+h (x 2))=
      fun x => scalarIncrementChain l f (x 0)+scalarIncrementChain l g (x 1)+scalarIncrementChain l h (x 2) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [tripleTailSchedule,List.flatMap_cons,vectorIncrementChain_append]
    simp only [tripleTailSchedule] at ih
    rw [ih,tripleTailBlock_value (scalarIncrementChain_regular l hf)
      (scalarIncrementChain_regular l hg) (scalarIncrementChain_regular l hh)]
    rfl

end SK.Analytic

end
end

end OAI
