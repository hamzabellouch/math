import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceWalls

namespace OAI

/-! The full reference-register basis diagonalizes every local Y operator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaReferenceTensor (n : ℕ) : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  sourceTensor n (fun _ => qmaReferenceBasis)

theorem qmaReferenceTensor_gram (n : ℕ) :
    (qmaReferenceTensor n).conjTranspose*qmaReferenceTensor n = 1 := by
  unfold qmaReferenceTensor
  rw [sourceTensor_conjTranspose,sourceTensor_mul]
  simp only [qmaReferenceBasis_gram]
  exact sourceTensor_one n

theorem qmaReferenceTensor_cogram (n : ℕ) :
    qmaReferenceTensor n*(qmaReferenceTensor n).conjTranspose = 1 := by
  exact mul_eq_one_comm.mp (qmaReferenceTensor_gram n)

theorem qmaReferenceTensor_y (n : ℕ) (i : Fin n) :
    (qmaReferenceTensor n).conjTranspose*sourceLocalPauli n i 1*qmaReferenceTensor n =
      sourceLocalPauli n i 2 := by
  unfold qmaReferenceTensor sourceLocalPauli
  rw [sourceTensor_conjTranspose,sourceTensor_mul,sourceTensor_mul]
  congr 1
  funext k
  by_cases hk : k = i
  · simp only [hk,ite_true]
    exact qmaReferenceBasis_y
  · simp only [hk,ite_false,mul_one,qmaReferenceBasis_gram]

theorem qmaReferenceTensor_yy (n : ℕ) (i j : Fin n) :
    (qmaReferenceTensor n).conjTranspose*
        (sourceLocalPauli n i 1*sourceLocalPauli n j 1)*qmaReferenceTensor n =
      sourceLocalPauli n i 2*sourceLocalPauli n j 2 := by
  rw [←qmaReferenceTensor_y n i,←qmaReferenceTensor_y n j]
  simp only [mul_assoc]
  rw [←mul_assoc (qmaReferenceTensor n),qmaReferenceTensor_cogram,one_mul]

end ContinuumCoulomb

end

end OAI
