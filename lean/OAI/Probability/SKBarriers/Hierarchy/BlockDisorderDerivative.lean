import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockDerivativeSum

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem disorderIndex_lt_blockLevel (D N k : ℕ) (i : Fin D) (l : Fin (k+1)) :
    (Fin.castAdd ((k+1)*N) i).val < (blockLevel D N k l).val := by
  rw [blockLevel_val]
  simp only [Fin.val_castAdd]
  omega

theorem blockPressure_disorder_coordinate {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) (i : Fin D) :
    fderiv ℝ (fun c : Fin (blockDimension D N k) → ℝ =>
      hierarchyPressure (blockDimension D N k) (blockMass D N k)
        (affineLogPartition (fun _ => 0) (spinExponent (blockDimension D N k) c (blockInteraction I))) 0)
      (blockCoefficients a v) (Pi.single (Fin.castAdd ((k+1)*N) i) 1) =
      a i * (1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ *
        (∫ z, (hierarchySpinMean (blockDimension D N k) (blockMass D N k) (blockExponent I a v)
          (fun s => spinMonomial s (I i)) (blockLevel D N k l) z)^2
          ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k)
            (affineLogPartition (fun _ => 0) (blockExponent I a v)) 0)) := by
  rw [spinPressure_coefficient_variation]
  simp only [blockCoefficients,blockInteraction,Fin.addCases_left]
  congr 2
  have he (j : Fin (blockDimension D N k+1)) (c : ℝ) :
      (if (Fin.castAdd ((k+1)*N) i).val < j.val then
        hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j*c else 0) =
      hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 j *
        (if (Fin.castAdd ((k+1)*N) i).val < j.val then c else 0) := by split_ifs <;> simp
  simp_rw [he]
  rw [blockAtom_sum_mul]
  simp only [disorderIndex_lt_blockLevel,ite_true]
  rfl
end SK.Analytic

end
end

end

end OAI
