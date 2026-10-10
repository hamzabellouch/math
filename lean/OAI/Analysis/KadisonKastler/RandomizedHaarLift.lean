import OAI.Analysis.KadisonKastler.FreeHaarTwists
import OAI.Analysis.KadisonKastler.UltrapowerExpectation
import OAI.Analysis.KadisonKastler.RecoveryWeakLimit
import OAI.Analysis.KadisonKastler.AmplificationPartition
import OAI.Analysis.KadisonKastler.RecoveryRowNormalization

namespace OAI

/-! # Free Haar moments for the actual randomized recovery lifts -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable {σ : FaithfulTracialState B}

/-- A constant unitary can be multiplied on the right of a free lift. -/
theorem freeHaar_mul_constant_right (π : BoundedSequence A →⋆ₐ[ℂ] B)
    (s : unitary (BoundedSequence A))
    (hs : FreeHaarMoments σ (π.comp boundedSequenceConst).range
      (Unitary.map (StarMonoidHom.ofClass π) s)) (U : unitary A) :
    FreeHaarMoments σ (π.comp boundedSequenceConst).range
      (Unitary.map (StarMonoidHom.ofClass π)
        (s * Unitary.map (StarMonoidHom.ofClass (boundedSequenceConst (B := A))) U)) := by
  rw [map_mul]
  exact hs.mul_right _ ⟨(U : A), rfl⟩

/-- A constant unitary can likewise be multiplied on the left. -/
theorem freeHaar_mul_constant_left (π : BoundedSequence A →⋆ₐ[ℂ] B)
    (s : unitary (BoundedSequence A))
    (hs : FreeHaarMoments σ (π.comp boundedSequenceConst).range
      (Unitary.map (StarMonoidHom.ofClass π) s)) (U : unitary A) :
    FreeHaarMoments σ (π.comp boundedSequenceConst).range
      (Unitary.map (StarMonoidHom.ofClass π)
        (Unitary.map (StarMonoidHom.ofClass (boundedSequenceConst (B := A))) U * s)) := by
  rw [map_mul]
  exact hs.mul_left _ ⟨(U : A), rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k q : ℕ} [NeZero q]

/-- The diagonal matrix phase is an actual unitary in the amplified algebra. -/
def amplificationPhaseUnitary (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (θ : Fin (n * k) → ZMod q) : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  ⟨diagonalPhase (amplificationPartition E) θ, diagonalPhase_mem_unitary _
    (fun a => (amplificationPartition_projection E a).isSelfAdjoint.star_eq)
    (fun a b => by
      split_ifs with hab
      · subst b; exact (amplificationPartition_projection E a).isIdempotentElem.eq
      · exact amplificationPartition_orthogonal E a b hab)
    (amplificationPartition_total E) θ⟩

/-- The three independent choices used in scalar recovery, as unitary sequences. -/
def randomizedRecoveryLift
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (θ : Fin (n * k) → ZMod q) (z : ZMod q) :
    unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) :=
  Unitary.map (StarMonoidHom.ofClass (boundedSequenceConst (B := Algebra (matrixVonNeumann (ι := Fin n) M)))) (scalarPhaseUnitary _ z) *
    (Unitary.map (StarMonoidHom.ofClass (boundedSequenceConst (B := Algebra (matrixVonNeumann (ι := Fin n) M)))) (amplificationPhaseUnitary E θ) *
      (s * Unitary.map (StarMonoidHom.ofClass (boundedSequenceConst (B := Algebra (matrixVonNeumann (ι := Fin n) M)))) U))

/-- Every member of the finite recovery family is free from the constant algebra. -/
theorem randomizedRecoveryLift_free
    (π : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M)) →⋆ₐ[ℂ] B)
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (hs : FreeHaarMoments σ (π.comp boundedSequenceConst).range
      (Unitary.map (StarMonoidHom.ofClass π) s))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (θ : Fin (n * k) → ZMod q) (z : ZMod q) :
    FreeHaarMoments σ (π.comp boundedSequenceConst).range
      (Unitary.map (StarMonoidHom.ofClass π) (randomizedRecoveryLift s U E θ z)) := by
  exact freeHaar_mul_constant_left π _
    (freeHaar_mul_constant_left π _ (freeHaar_mul_constant_right π s hs U)
      (amplificationPhaseUnitary E θ)) (scalarPhaseUnitary _ z)

/-- Evaluation of the finite randomized family gives exactly the scalar
phase twist of the diagonal-phase unitary used by the row formulas. -/
theorem randomizedRecoveryLift_eval
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (θ : Fin (n * k) → ZMod q) (z : ZMod q) (j : ℕ) :
    sequenceUnitaryEval (randomizedRecoveryLift s U E θ z) j =
      scalarPhaseTwist z (amplificationPhaseUnitary E θ * (sequenceUnitaryEval s j * U)) := by
  apply Subtype.ext
  rfl

end

end KadisonKastler

end OAI
