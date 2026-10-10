import OAI.NumberTheory.DirichletL.Reflection.PhysicalBranchMeasure

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory FourierBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma weightedKernelCoordinate_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (i : Fin 4) (slope Q t q : ℝ) :
    ‖a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q‖≤1 := by
  rw [norm_mul,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (reciprocalKernelWindows_norm windows M hw hs i _)

lemma weightedKernelDual_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (Qn Qb t n b : ℝ) :
    ‖a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b‖≤1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans
    (kernelDualWeight_norm_le_one _ (reciprocalKernelWindows_norm windows M hw hs) Qn Qb t n b)

lemma weightedKernelCoordinate_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (i : Fin 4) (slope Q q : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q) :=
  ((kernelCoordinateWeight_continuous _ _ _ _).const_mul a).aestronglyMeasurable

lemma weightedKernelDual_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (Qn Qb n b : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b) := by
  exact (((kernelCoordinateWeight_continuous _ _ _ _).mul
    (kernelCoordinateWeight_continuous _ _ _ _)).const_mul a).aestronglyMeasurable

end
end SevenEighths.InverseReflectedPhase

end OAI
