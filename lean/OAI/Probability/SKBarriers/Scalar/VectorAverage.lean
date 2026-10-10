import Mathlib
import OAI.Probability.SKBarriers.Replicas.PairRecursion

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorHierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (Fin n → E) →
    (E → ℝ) → (E → ℝ) → E → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => vectorHierarchyAverage n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last n)) (v (Fin.last n)) f)
      (vectorStepAverage (m (Fin.last n)) (v (Fin.last n)) f g)

theorem hierarchyAverage_vector_linear (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (f g : E → ℝ) (c : ℝ → E) :
    hierarchyAverage n m (fun z => f (c (parameter n z)+∑ j, coordinateProjection n j z • v j))
      (fun z => g (c (parameter n z)+∑ j, coordinateProjection n j z • v j))=
      fun x => vectorHierarchyAverage n m v f g (c x) := by
  induction n generalizing f g with
  | zero => simp [hierarchyAverage,vectorHierarchyAverage,parameter]
  | succ n ih =>
    have he (F : E → ℝ) : (fun z : ParameterSpace (n+1) =>
        F (c (parameter (n+1) z)+∑ j, coordinateProjection (n+1) j z • v j))=
        fun z => F ((c (parameter n z.1)+∑ j : Fin n, coordinateProjection n j z.1 • v j.castSucc)+
          z.2 • v (Fin.last n)) := by
      funext z
      rw [Fin.sum_univ_castSucc]
      simp [coordinateProjection,parameter,add_assoc]
    rw [he f,he g,hierarchyAverage]
    change hierarchyAverage n (fun j => m j.castSucc)
      (fun z => vectorStep (m (Fin.last n)) (v (Fin.last n)) f
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))
      (fun z => vectorStepAverage (m (Fin.last n)) (v (Fin.last n)) f g
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))=_
    rw [ih]
    rfl

theorem vectorHierarchy_split (a b : ℕ) (m : Fin (a+b) → ℝ) (v : Fin (a+b) → E) (f : E → ℝ) :
    vectorHierarchy (a+b) m v f=
      vectorHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  induction b generalizing f with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)

theorem vectorHierarchyAverage_split (a b : ℕ) (m : Fin (a+b) → ℝ) (v : Fin (a+b) → E)
    (f g : E → ℝ) :
    vectorHierarchyAverage (a+b) m v f g=
      vectorHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (vectorHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g) := by
  induction b generalizing f g with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
      (vectorStepAverage (m (Fin.last (a+b))) (v (Fin.last (a+b))) f g)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorStep_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f : F → ℝ) :
    vectorStep m v (f ∘ L)=vectorStep m (L v) f ∘ L := by
  funext x
  simp only [vectorStep,Function.comp_def,map_add,map_smul]
  rfl

theorem vectorStepAverage_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f g : F → ℝ) :
    vectorStepAverage m v (f ∘ L) (g ∘ L)=vectorStepAverage m (L v) f g ∘ L := by
  funext x
  simp only [vectorStepAverage,Function.comp_def,map_add,map_smul]
  rfl

theorem vectorHierarchy_pullback (L : E →L[ℝ] F) (n : ℕ) (m : Fin n → ℝ)
    (v : Fin n → E) (f : F → ℝ) :
    vectorHierarchy n m v (f ∘ L)=vectorHierarchy n m (L ∘ v) f ∘ L := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchy,vectorStep_pullback,ih]
    rfl

theorem vectorHierarchyAverage_pullback (L : E →L[ℝ] F) (n : ℕ) (m : Fin n → ℝ)
    (v : Fin n → E) (f g : F → ℝ) :
    vectorHierarchyAverage n m v (f ∘ L) (g ∘ L)=vectorHierarchyAverage n m (L ∘ v) f g ∘ L := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchyAverage,vectorStep_pullback,vectorStepAverage_pullback,ih]
    rfl
end Vector

end SK.Analytic

end
end

end OAI
