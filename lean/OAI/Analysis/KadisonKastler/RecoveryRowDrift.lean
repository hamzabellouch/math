import OAI.Analysis.KadisonKastler.RecoveryRowNormalization
import OAI.Analysis.KadisonKastler.RandomizedRMS
import OAI.Analysis.KadisonKastler.ScalarAmplification

namespace OAI

/-! # Recovery-row drift from the actual errors of the unitary powers -/

namespace KadisonKastler

open Finset Filter
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

/-- The diagonal amplification applies the original operator in each coordinate. -/
theorem diagonalAmplification_coordinate_compatibility (h : H →L[ℂ] H)
    (x : Generator.FiniteHilbert (Fin n) H) (a : Fin n) :
    h (x a) = (hilbertMatrix (diagonalAmplification (n := Fin n) h) x) a := by
  rw [hilbertMatrix_apply]
  simp only [diagonalAmplification, diagonalStarAlgHom_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

variable {I Ω : Type*} [Fintype I]

omit [CompleteSpace H] in
/-- Coordinate compatibility transports a phase sum of power errors to the
error of the corresponding normalized row. -/
theorem normalized_phase_row_error
    (h : H →L[ℂ] H)
    (T : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H)
    (hcoord : ∀ x : Generator.FiniteHilbert (Fin n) H, ∀ a, h (x a) = (T x) a)
    (χ : I → Ω → ℂ) (X Y : I → Generator.FiniteHilbert (Fin n) H)
    (s t : ℝ) (z : Ω) (a : Fin n) :
    h (s • (t • finitePhaseSum χ X z) a) - s • (t • finitePhaseSum χ Y z) a =
      s • (t • finitePhaseSum χ (fun r => T (X r) - Y r) z) a := by
  simp [finitePhaseSum, ← hcoord,
    smul_sub, Finset.sum_sub_distrib]

variable {Θ : Type*} [Fintype Θ] [Nonempty Θ] {q N : ℕ} [NeZero q]

/-- A uniform power-error bound in RMS gives the same bound for the actual
forward recovery rows after the independent scalar phase and coordinate choice. -/
theorem recoveryForwardRows_drift_le (M : VonNeumannAlgebra H)
    (h : H →L[ℂ] H)
    (T : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H)
    (hcoord : ∀ x : Generator.FiniteHilbert (Fin n) H, ∀ a, h (x a) = (T x) a)
    (v : Θ → unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (ξ ζ : Generator.FiniteHilbert (Fin n) H)
    (hN : 0 < N) (hNq : N < q) {C : ℝ}
    (hpower : ∀ r : Fin N, finiteRMS (fun θ =>
      T ((((v θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ξ) -
        (((v θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ζ) ≤ C) :
    finiteRMS (fun t : (Θ × ZMod q) × Fin n =>
      h (recoveryForwardRow M N t.2 (scalarPhaseTwist t.1.2 (v t.1.1)) ξ) -
        recoveryForwardRow M N t.2 (scalarPhaseTwist t.1.2 (v t.1.1)) ζ) ≤ C := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hC : 0 ≤ C := (finiteRMS_nonneg _).trans (hpower ⟨0, hN⟩)
  have hb := phase_basis_double_rms_le
    (fun r : Fin N => scalarPowerCharacter q N r)
    (scalarPowerCharacter_orthogonal hNq)
    (fun r θ =>
      T ((((v θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ξ) -
        (((v θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ζ)
    hC hpower
  simp only [Fintype.card_fin] at hb
  simpa only [recoveryForwardRow_phase_apply,
    normalized_phase_row_error h T hcoord] using hb

/-- The adjoint power errors control the backward rows, with comparison
vector `T ξ` as needed in the scalar quadratic estimate. -/
theorem recoveryBackwardRows_drift_le (M : VonNeumannAlgebra H)
    (h : H →L[ℂ] H)
    (T : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H)
    (hcoord : ∀ x : Generator.FiniteHilbert (Fin n) H, ∀ a, h (x a) = (T x) a)
    (v : Θ → unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (ξ : Generator.FiniteHilbert (Fin n) H)
    (hN : 0 < N) (hNq : N < q) {C : ℝ}
    (hpower : ∀ r : Fin N, finiteRMS (fun θ =>
      T (((star ((v θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1))).val) ξ) -
        ((star ((v θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1))).val) (T ξ)) ≤ C) :
    finiteRMS (fun t : (Θ × ZMod q) × Fin n =>
      h (recoveryBackwardRow M N t.2 (scalarPhaseTwist t.1.2 (v t.1.1)) ξ) -
        recoveryBackwardRow M N t.2 (scalarPhaseTwist t.1.2 (v t.1.1)) (T ξ)) ≤ C := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hC : 0 ≤ C := (finiteRMS_nonneg _).trans (hpower ⟨0, hN⟩)
  have hb := phase_basis_double_rms_le
    (fun r : Fin N => ⇑((scalarPowerCharacter q N r)⁻¹ : AddChar (ZMod q) ℂ))
    (inverseScalarPowerCharacter_orthogonal hNq)
    (fun r θ =>
      T (((star ((v θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1))).val) ξ) -
        ((star ((v θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1))).val) (T ξ))
    hC hpower
  simp only [Fintype.card_fin] at hb
  simpa only [recoveryBackwardRow_phase_apply,
    normalized_phase_row_error h T hcoord] using hb


variable {J : Type*}

/-- Finitely many eventual power bounds give the eventual forward-row bound
with the same arbitrary error tolerance. -/
theorem eventually_recoveryForwardRows_drift_le (M : VonNeumannAlgebra H)
    (l : Filter J) (h : H →L[ℂ] H)
    (T : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H)
    (hcoord : ∀ x : Generator.FiniteHilbert (Fin n) H, ∀ a, h (x a) = (T x) a)
    (v : J → Θ → unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (ξ ζ : Generator.FiniteHilbert (Fin n) H)
    (hN : 0 < N) (hNq : N < q) {C : ℝ}
    (hpower : ∀ r : Fin N, ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun θ =>
        T ((((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ξ) -
          (((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ζ) ≤
            C + ε) :
    ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun t : (Θ × ZMod q) × Fin n =>
        h (recoveryForwardRow M N t.2 (scalarPhaseTwist t.1.2 (v j t.1.1)) ξ) -
          recoveryForwardRow M N t.2 (scalarPhaseTwist t.1.2 (v j t.1.1)) ζ) ≤ C + ε := by
  intro ε hε
  have hall : ∀ᶠ j in l, ∀ r : Fin N,
      finiteRMS (fun θ =>
        T ((((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ξ) -
          (((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val) ζ) ≤
            C + ε := eventually_all.mpr (fun r => hpower r ε hε)
  filter_upwards [hall] with j hj
  exact recoveryForwardRows_drift_le M h T hcoord (v j) ξ ζ hN hNq hj

/-- The same finite intersection of eventual events controls the backward rows. -/
theorem eventually_recoveryBackwardRows_drift_le (M : VonNeumannAlgebra H)
    (l : Filter J) (h : H →L[ℂ] H)
    (T : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H)
    (hcoord : ∀ x : Generator.FiniteHilbert (Fin n) H, ∀ a, h (x a) = (T x) a)
    (v : J → Θ → unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (ξ : Generator.FiniteHilbert (Fin n) H)
    (hN : 0 < N) (hNq : N < q) {C : ℝ}
    (hpower : ∀ r : Fin N, ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun θ =>
        T (((star ((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
          (r.val + 1))).val) ξ) -
        ((star ((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
          (r.val + 1))).val) (T ξ)) ≤ C + ε) :
    ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun t : (Θ × ZMod q) × Fin n =>
        h (recoveryBackwardRow M N t.2 (scalarPhaseTwist t.1.2 (v j t.1.1)) ξ) -
          recoveryBackwardRow M N t.2 (scalarPhaseTwist t.1.2 (v j t.1.1)) (T ξ)) ≤ C + ε := by
  intro ε hε
  have hall : ∀ᶠ j in l, ∀ r : Fin N,
      finiteRMS (fun θ =>
        T (((star ((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
          (r.val + 1))).val) ξ) -
        ((star ((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
          (r.val + 1))).val) (T ξ)) ≤ C + ε :=
    eventually_all.mpr (fun r => hpower r ε hε)
  filter_upwards [hall] with j hj
  exact recoveryBackwardRows_drift_le M h T hcoord (v j) ξ hN hNq hj

end

end KadisonKastler

end OAI
