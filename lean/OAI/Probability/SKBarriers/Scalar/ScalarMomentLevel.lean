import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSymmetry
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
import OAI.Probability.SKBarriers.Scalar.ScalarSplit

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_scalar_split (a b : ℕ) (m v : Fin (a+b) → ℝ)
    (F G : ℝ → ℝ → ℝ) (c : ℝ) (z : ParameterSpace (a+b)) :
    hierarchyMomentLevel (a+b) m (scalarParameterTerminal (a+b) v F c)
      (scalarParameterTerminal (a+b) v G c) ⟨a,by omega⟩ z =
      scalarHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a))
        (F (parameter (a+b) z)) (G (parameter (a+b) z))
        (c+∑ i : Fin a, v (i.castAdd b)*coordinateProjection (a+b) (i.castAdd b) z) := by
  induction b generalizing F G with
  | zero =>
    have he : (⟨a,by omega⟩ : Fin (a+1))=Fin.last a := rfl
    rw [he]
    cases a with
    | zero => simp [hierarchyMomentLevel,scalarHierarchyAverage,scalarParameterTerminal,coordinateLinear]
    | succ a =>
      simp only [hierarchyMomentLevel,Fin.lastCases_last,scalarHierarchyAverage]
      change G (parameter (a+1) z) (c+coordinateLinear (a+1) v z) = _
      rw [coordinateLinear_apply]
      rfl
  | succ b ih =>
    change hierarchyMomentLevel (a+b+1) m (scalarParameterTerminal (a+b+1) v F c)
      (scalarParameterTerminal (a+b+1) v G c) (Fin.castSucc ⟨a,by omega⟩) z = _
    simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,
      gaussianStep_scalarParameterTerminal,gaussianAverage_scalarParameterTerminal]
    rw [ih]
    change scalarHierarchyAverage b _ _ _ _ _ = scalarHierarchyAverage b _ _ _ _ _
    congr 1
    apply congrArg (c+·)
    apply Finset.sum_congr rfl
    intro i _
    have he : (i.castAdd b).castSucc=i.castAdd (b+1) := by ext; rfl
    rw [← he]
    change _ = v (i.castAdd b).castSucc * coordinateProjection (a+b+1) (i.castAdd b).castSucc z
    rw [coordinateProjection_castSucc]

theorem scalarHierarchyAverage_spin_abs_le_field (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (x : ℝ) :
    |scalarHierarchyAverage n m v scalarSpinTerminal scalarMagnetization x| ≤ |x| := by
  rw [← scalarHierarchy_gradient_average n m v scalarSpinTerminal_regular scalarSpinTerminal_hasDerivAt]
  change |rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) x| ≤ |x|
  have H := (scalarHierarchy_spin_gradient_lipschitz n m v hm).norm_sub_le x 0
  have h0 : rootGradient 0 (scalarHierarchy n m v scalarSpinTerminal) 0=0 :=
    scalarHierarchy_spin_gradient_zero n m v
  simpa only [h0,sub_zero,Real.norm_eq_abs,NNReal.coe_one,one_mul] using H

end SK.Analytic

end
end

end OAI
