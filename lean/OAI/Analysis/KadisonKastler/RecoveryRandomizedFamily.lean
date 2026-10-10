import OAI.Analysis.KadisonKastler.RecoveryRowAverages
import OAI.Analysis.KadisonKastler.RecoveryFamilyNormalization
import OAI.Analysis.KadisonKastler.RandomizedHaarLift

namespace OAI

/-! # The actual randomized recovery family

The diagonal phase, scalar phase, and outer coordinate are the three finite
choices used in the recovery argument. Their rows have exact normalization,
the corner operators are contractions in the original algebra, and the row
product converges to a scalar with real part at least one half.
-/

namespace KadisonKastler

open Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k q N : ℕ} [NeZero q]

/-- The finite unitary family before the final coordinate-row choice. -/
def randomizedRecoveryFamily
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M)) :
    ((Fin (n * k) → ZMod q) × ZMod q) →
      unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) :=
  fun t => randomizedRecoveryLift s U E t.1 t.2

/-- The exact forward RMS normalization holds at every sequence coordinate. -/
theorem randomizedRecoveryFamily_forward_finiteRMS
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (hN : 0 < N) (hNq : N < q) (j : ℕ) (ξ : Generator.FiniteHilbert (Fin n) H) :
    finiteRMS (fun t : ((Fin (n * k) → ZMod q) × ZMod q) × Fin n =>
      recoverySequenceForwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t ξ) = ‖ξ‖ := by
  have hh := recoveryForwardFamily_finiteRMS M
    (fun θ : Fin (n * k) → ZMod q =>
      amplificationPhaseUnitary E θ * (sequenceUnitaryEval s j * U)) hN hNq ξ
  simpa only [recoverySequenceForwardRows, randomizedRecoveryFamily,
    randomizedRecoveryLift_eval] using hh

/-- The same exact normalization holds for the backward rows. -/
theorem randomizedRecoveryFamily_backward_finiteRMS
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (hN : 0 < N) (hNq : N < q) (j : ℕ) (ξ : Generator.FiniteHilbert (Fin n) H) :
    finiteRMS (fun t : ((Fin (n * k) → ZMod q) × ZMod q) × Fin n =>
      recoverySequenceBackwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t ξ) = ‖ξ‖ := by
  have hh := recoveryBackwardFamily_finiteRMS M
    (fun θ : Fin (n * k) → ZMod q =>
      amplificationPhaseUnitary E θ * (sequenceUnitaryEval s j * U)) hN hNq ξ
  simpa only [recoverySequenceBackwardRows, randomizedRecoveryFamily,
    randomizedRecoveryLift_eval] using hh

/-- The extracted operators stay inside the unit ball of the original factor. -/
theorem randomizedRecoveryFamily_contractions_norm_le
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M)) (hn : 0 < n)
    (N j : ℕ) (t : ((Fin (n * k) → ZMod q) × ZMod q) × Fin n) :
    ‖recoverySequenceContractions M N (randomizedRecoveryFamily (q := q) s U E) j t‖ ≤ 1 :=
  recoverySequenceContractions_norm_le M hn N _ j t

variable [NeZero n]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {P : VonNeumannAlgebra K} {τ : FaithfulTracialState (Algebra M)}
variable {σ : FaithfulTracialState (Algebra P)} {ω : Ultrafilter ℕ}

/-- Free Haar moments for the starting lift suffice for the scalar weak limit
of this specific randomized family; every phase twist is proved free. -/
theorem TraceQuotientMap.exists_randomizedRecoveryFamily_weak_scalar
    (D : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
    (hτ : FiniteVectorTrace τ) (hσ : FiniteVectorTrace σ)
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (hs : FreeHaarMoments σ D.constant.range
      (Unitary.map (StarMonoidHom.ofClass D.quotient) s))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (hn : 2 ≤ n) (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N) :
    ∃ c : ℂ, 1 / 2 ≤ c.re ∧
      WeakOperatorConverges (ω : Filter ℕ)
        (fun j => averageRowProduct
          (recoverySequenceForwardRows M N (randomizedRecoveryFamily (q := q) s U E) j)
          (recoverySequenceBackwardRows M N (randomizedRecoveryFamily (q := q) s U E) j)
          (fun t => (recoverySequenceContractions M N (randomizedRecoveryFamily (q := q) s U E) j t).val))
        (c • ContinuousLinearMap.id ℂ (Generator.FiniteHilbert (Fin n) H)) := by
  apply D.exists_recoveryRows_weak_scalar hτ hσ (randomizedRecoveryFamily (q := q) s U E)
    (fun t => Unitary.map (StarMonoidHom.ofClass D.quotient)
      (randomizedRecoveryFamily (q := q) s U E t)) (fun _ => rfl) ?_ hn hsize
  intro t
  exact randomizedRecoveryLift_free D.quotient s hs U E t.1 t.2

end

end KadisonKastler

end OAI
