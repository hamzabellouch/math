import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleTailValue
import OAI.Probability.SKBarriers.Scalar.VectorAverageRegular

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorIncrementAverage_pullback (L : E →L[ℝ] F) (l : List (ℝ × E)) (f g : F → ℝ) :
    vectorIncrementAverage l (f ∘ L) (g ∘ L)=
      vectorIncrementAverage (l.map (fun p => (p.1,L p.2))) f g ∘ L := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vectorIncrementAverage,vectorIncrementChain_pullback,ih,vectorStepAverage_pullback]
    rfl

theorem vectorIncrementChain_get (l : List (ℝ × E)) (f : E → ℝ) :
    vectorIncrementChain l f=vectorHierarchy l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f := by
  simpa only [Prod.mk.eta,List.ofFn_get] using
    vectorIncrementChain_ofFn l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f

theorem vectorIncrementAverage_get (l : List (ℝ × E)) (f g : E → ℝ) :
    vectorIncrementAverage l f g=vectorHierarchyAverage l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g := by
  simpa only [Prod.mk.eta,List.ofFn_get] using
    vectorIncrementAverage_ofFn l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g

theorem vectorIncrementAverage_regular (l : List (ℝ × E)) {f g : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (he : HasExpGrowth g) :
    Continuous (vectorIncrementAverage l f g) ∧ HasExpGrowth (vectorIncrementAverage l f g) := by
  rw [vectorIncrementAverage_get]
  exact vectorHierarchyAverage_regular _ _ _ hf he hg
end Vector

theorem vectorIncrementAverage_real (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    vectorIncrementAverage l f g=scalarIncrementAverage l f g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vectorIncrementAverage,scalarIncrementAverage,vectorIncrementChain_real,ih,vectorStepAverage_real]

theorem scalarIncrementChain_ofFn (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) :
    scalarIncrementChain (List.ofFn (fun i => (m i,v i))) f=scalarHierarchy n m v f := by
  rw [← vectorIncrementChain_real,vectorIncrementChain_ofFn,vectorHierarchy_real]

theorem scalarIncrementAverage_ofFn (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    scalarIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=scalarHierarchyAverage n m v f g := by
  rw [← vectorIncrementAverage_real,vectorIncrementAverage_ofFn,vectorHierarchyAverage_real]

theorem scalarIncrementChain_get (l : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    scalarIncrementChain l f=scalarHierarchy l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f := by
  rw [← vectorIncrementChain_real,vectorIncrementChain_get,vectorHierarchy_real]

theorem scalarIncrementAverage_get (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    scalarIncrementAverage l f g=scalarHierarchyAverage l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f g := by
  rw [← vectorIncrementAverage_real,vectorIncrementAverage_get,vectorHierarchyAverage_real]

theorem scalarIncrementChain_append (l r : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    scalarIncrementChain (l++r) f=scalarIncrementChain l (scalarIncrementChain r f) := by
  simp only [← vectorIncrementChain_real,vectorIncrementChain_append]

theorem scalarIncrementAverage_append (l r : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (l++r) f g=scalarIncrementAverage l (scalarIncrementChain r f) (scalarIncrementAverage r f g) := by
  simp only [← vectorIncrementAverage_real,← vectorIncrementChain_real,vectorIncrementAverage_append]

end SK.Analytic

end
end

end OAI
