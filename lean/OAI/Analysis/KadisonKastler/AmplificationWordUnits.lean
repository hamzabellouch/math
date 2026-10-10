import OAI.Analysis.KadisonKastler.RandomizedHaarLift

namespace OAI

/-! # The unitary words used by coefficient and row estimates -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k q : ℕ} [NeZero q]

/-- The base word after the independent diagonal phase. -/
def phaseWordBase (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (θ : Fin (n * k) → ZMod q) : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  amplificationPhaseUnitary E θ * v

/-- Positive word with its last free-unitary factor removed. -/
def positivePhaseWordUnitary (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (r : ℕ) (θ : Fin (n * k) → ZMod q) :
    unitary (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  phaseWordBase E v θ ^ r * amplificationPhaseUnitary E θ

/-- Negative word, already a full adjoint power. -/
def negativePhaseWordUnitary (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (r : ℕ) (θ : Fin (n * k) → ZMod q) :
    unitary (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  star (phaseWordBase E v θ ^ (r + 1))

theorem positivePhaseWordUnitary_coe
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (r : ℕ) (θ : Fin (n * k) → ZMod q) :
    (positivePhaseWordUnitary E v r θ : Algebra (matrixVonNeumann (ι := Fin n) M)) =
      (diagonalPhase (amplificationPartition E) θ * (v : Algebra _)) ^ r *
        diagonalPhase (amplificationPartition E) θ := by
  simp only [positivePhaseWordUnitary, phaseWordBase, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  rfl

theorem negativePhaseWordUnitary_coe
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (r : ℕ) (θ : Fin (n * k) → ZMod q) :
    (negativePhaseWordUnitary E v r θ : Algebra (matrixVonNeumann (ι := Fin n) M)) =
      (star (v : Algebra _) * star (diagonalPhase (amplificationPartition E) θ)) ^ (r + 1) := by
  simp only [negativePhaseWordUnitary, phaseWordBase, Unitary.coe_star,
    SubmonoidClass.coe_pow, Submonoid.coe_mul, star_pow, star_mul]
  rfl

/-- Appending the removed factor recovers the exact power used in the row. -/
theorem positivePhaseWordUnitary_mul
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (v : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (r : ℕ) (θ : Fin (n * k) → ZMod q) :
    positivePhaseWordUnitary E v r θ * v = phaseWordBase E v θ ^ (r + 1) := by
  rw [positivePhaseWordUnitary, mul_assoc, ← phaseWordBase, pow_succ]

end

end KadisonKastler

end OAI
