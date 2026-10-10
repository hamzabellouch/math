import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterSpace
import OAI.Probability.SKBarriers.Hierarchy.CascadeProbability

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section CascadeMap
variable {E F : Type}

def cascadeMap : (n : ℕ) → (E → F) → CascadeSpace E n → CascadeSpace F n
  | 0,A => A
  | n+1,A => fun z => (cascadeMap n A z.1,z.2)

theorem gaussianStep_cascadeMap (n : ℕ) (A : E → F) (p : ℝ)
    (f : CascadeSpace F (n+1) → ℝ) :
    gaussianStep p (fun z => f (cascadeMap (n+1) A z)) =
      fun z => gaussianStep p f (cascadeMap n A z) := rfl

theorem gaussianAverage_cascadeMap (n : ℕ) (A : E → F) (p : ℝ)
    (f g : CascadeSpace F (n+1) → ℝ) :
    gaussianAverage p (fun z => f (cascadeMap (n+1) A z)) (fun z => g (cascadeMap (n+1) A z)) =
      fun z => gaussianAverage p f g (cascadeMap n A z) := rfl

theorem cascadePressure_cascadeMap (n : ℕ) (A : E → F) (m : Fin n → ℝ)
    (f : CascadeSpace F n → ℝ) (x : E) :
    cascadePressure n m (fun z => f (cascadeMap n A z)) x = cascadePressure n m f (A x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cascadePressure,gaussianStep_cascadeMap,ih,cascadePressure]

theorem cascadeMoment_cascadeMap (n : ℕ) (A : E → F) (m : Fin n → ℝ)
    (f g : CascadeSpace F n → ℝ) (x : E) :
    cascadeMoment n m (fun z => f (cascadeMap n A z)) (fun z => g (cascadeMap n A z)) x =
      cascadeMoment n m f g (A x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cascadeMoment,gaussianStep_cascadeMap,gaussianAverage_cascadeMap,ih,cascadeMoment]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def cascadeMapCLM : (n : ℕ) → (E →L[ℝ] F) → CascadeSpace E n →L[ℝ] CascadeSpace F n
  | 0,A => A
  | n+1,A => (cascadeMapCLM n A).prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem cascadeMapCLM_apply (n : ℕ) (A : E →L[ℝ] F) (z : CascadeSpace E n) :
    cascadeMapCLM n A z = cascadeMap n A z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cascadeMapCLM n A z.1,z.2) = (cascadeMap n A z.1,z.2)
    rw [ih]

theorem cascadeMap_affine (n : ℕ) (u : F) (A : E →L[ℝ] F) (z : CascadeSpace E n) :
    cascadeMap n (fun x => u+A x) z = cascadeLift n u+cascadeMapCLM n A z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cascadeMap n (fun x => u+A x) z.1,z.2) = (cascadeLift n u+cascadeMapCLM n A z.1,0+z.2)
    rw [ih,zero_add]

theorem cascadeMapCLM_lift (n : ℕ) (A : E →L[ℝ] F) (x : E) :
    cascadeMapCLM n A (cascadeLift n x) = cascadeLift n (A x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cascadeMapCLM n A (cascadeLift n x),0) = (cascadeLift n (A x),0)
    rw [ih]

variable {S : Type} [Fintype S]

def rebaseConstants (n : ℕ) (c : S → ℝ) (L : S → CascadeSpace F n →L[ℝ] ℝ) (u : F) : S → ℝ :=
  fun s => c s+L s (cascadeLift n u)

def rebaseLinears (n : ℕ) (L : S → CascadeSpace F n →L[ℝ] ℝ) (A : E →L[ℝ] F) :
    S → CascadeSpace E n →L[ℝ] ℝ := fun s => (L s).comp (cascadeMapCLM n A)

theorem affineLogPartition_rebase (n : ℕ) (c : S → ℝ) (L : S → CascadeSpace F n →L[ℝ] ℝ)
    (u : F) (A : E →L[ℝ] F) :
    affineLogPartition (rebaseConstants n c L u) (rebaseLinears n L A) =
      fun z => affineLogPartition c L (cascadeMap n (fun x => u+A x) z) := by
  funext z
  simp only [affineLogPartition,rebaseConstants,rebaseLinears,
    ContinuousLinearMap.comp_apply,cascadeMap_affine,map_add,add_assoc]

theorem affineGibbs_rebase (n : ℕ) (c : S → ℝ) (L : S → CascadeSpace F n →L[ℝ] ℝ)
    (u : F) (A : E →L[ℝ] F) (z : CascadeSpace E n) (s : S) :
    affineGibbs (rebaseConstants n c L u) (rebaseLinears n L A) z s =
      affineGibbs c L (cascadeMap n (fun x => u+A x) z) s := by
  simp only [affineGibbs,rebaseConstants,rebaseLinears,
    ContinuousLinearMap.comp_apply,cascadeMap_affine,map_add,add_assoc]

theorem cascadePressure_rebase (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (L : S → CascadeSpace F n →L[ℝ] ℝ) (u : F) (A : E →L[ℝ] F) (x : E) :
    cascadePressure n m (affineLogPartition (rebaseConstants n c L u) (rebaseLinears n L A)) x =
      cascadePressure n m (affineLogPartition c L) (u+A x) := by
  rw [affineLogPartition_rebase,cascadePressure_cascadeMap]

theorem cascadeSpinWeight_rebase (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (L : S → CascadeSpace F n →L[ℝ] ℝ) (u : F) (A : E →L[ℝ] F) (x : E) (s : S) :
    cascadeSpinWeight n m (rebaseConstants n c L u) (rebaseLinears n L A) x s =
      cascadeSpinWeight n m c L (u+A x) s := by
  unfold cascadeSpinWeight
  rw [affineLogPartition_rebase]
  simp only [affineGibbs_rebase]
  exact cascadeMoment_cascadeMap n (fun x => u+A x) m (affineLogPartition c L) (fun z => affineGibbs c L z s) x
end CascadeMap
end SK.Analytic

end
end

end

end OAI
