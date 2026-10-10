import OAI.Analysis.Laughlin.Spin.CopySchur
import OAI.Analysis.Laughlin.Spin.Disjoint
import OAI.Analysis.Laughlin.Spin.RectangularAverage

namespace OAI

namespace Laughlin.Rotation
open scoped Matrix

theorem source_unequal_spin_haar_zero (m n : ℕ) (hmn : m ≠ n)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ) :
    rectangularIntegral sourceHaar
      (rectangularOrbit (sourceSpinRepresentation m) (sourceSpinRepresentation n) M)=0 := by
  exact source_spin_intertwiner_zero m n hmn _
    (compact_rectangular_average_intertwines sourceHaar _ _
      (sourceSpinRepresentation_continuous m) (sourceSpinRepresentation_continuous n) M)

theorem source_equal_spin_haar_trace (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :
    rectangularIntegral sourceHaar
      (rectangularOrbit (sourceSpinRepresentation Q) (sourceSpinRepresentation Q) M)=
      (Matrix.trace M/(Q+1 : ℕ)) • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :=
  source_spin_haar_schur Q M

end Laughlin.Rotation

end OAI
