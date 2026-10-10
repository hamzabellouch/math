import OAI.Analysis.KadisonKastler.RecoveryRandomizedFamily
import OAI.Analysis.KadisonKastler.RecoveryRowDrift
import OAI.Analysis.KadisonKastler.ComplexRowExtraction

namespace OAI

/-! # The quadratic estimate from the actual randomized recovery family -/

namespace KadisonKastler

open Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

/-- The matrix and direct-sum definitions of diagonal amplification agree. -/
theorem hilbertMatrix_diagonalAmplification_eq (h : H →L[ℂ] H) :
    hilbertMatrix (diagonalAmplification (n := Fin n) h) =
      Generator.diagonalOperator (ι := Fin n) h := by
  ext x a
  exact (diagonalAmplification_coordinate_compatibility h x a).symm

/-- A symmetric operator remains selfadjoint after diagonal amplification. -/
theorem diagonalAmplification_isSelfAdjoint (h : H →L[ℂ] H) (hh : h.IsSymmetric) :
    IsSelfAdjoint (hilbertMatrix (diagonalAmplification (n := Fin n) h)) := by
  change star (hilbertMatrix (diagonalAmplification (n := Fin n) h)) = _
  rw [hilbertMatrix_diagonalAmplification_eq, ← Generator.diagonalOperator_star,
    hh.isSelfAdjoint.star_eq]

variable {M : VonNeumannAlgebra H} {k q N : ℕ} [NeZero n] [NeZero q]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {P : VonNeumannAlgebra K} {τ : FaithfulTracialState (Algebra M)}
variable {σ : FaithfulTracialState (Algebra P)} {ω : Ultrafilter ℕ}

/-- The two actual eventual row-error estimates, the scalar derivation bound,
and the constructed recovery family imply the `282δ` quadratic estimate.
The row-error hypotheses are the only analytic assembly premises here. -/
theorem randomized_recovery_quadratic_bound
    (D : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
    (hτ : FiniteVectorTrace τ) (hσ : FiniteVectorTrace σ)
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (hs : FreeHaarMoments σ D.constant.range
      (Unitary.map (StarMonoidHom.ofClass D.quotient) s))
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (h : H →L[ℂ] H) (hh : h.IsSymmetric) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (hn : 2 ≤ n) (hN : 0 < N) (hNq : N < q)
    (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N)
    (ξ : Generator.FiniteHilbert (Fin n) H) (hξ : ‖ξ‖ = 1)
    (hforward : ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      finiteRMS (fun t : ((Fin (n * k) → ZMod q) × ZMod q) × Fin n =>
        h (recoverySequenceForwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t ξ) -
          recoverySequenceForwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t
            ((star U.val.val) (T (U.val.val ξ)))) ≤ 70 * δ + ε)
    (hbackward : ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      finiteRMS (fun t : ((Fin (n * k) → ZMod q) × ZMod q) × Fin n =>
        h (recoverySequenceBackwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t ξ) -
          recoverySequenceBackwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t
            (T ξ)) ≤ 70 * δ + ε) :
    let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
    |(inner ℂ (T ξ) ξ).re - (inner ℂ (T (U.val.val ξ)) (U.val.val ξ)).re| ≤ 282 * δ := by
  let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
  let u : unitary (Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) :=
    Unitary.map (StarMonoidHom.ofClass (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype) U
  let v := randomizedRecoveryFamily (q := q) s U E
  let F := recoverySequenceForwardRows M N v
  let G := recoverySequenceBackwardRows M N v
  let x := fun j t => (recoverySequenceContractions M N v j t).val
  have hn0 : 0 < n := by omega
  have hx : ∀ j t, ‖x j t‖ ≤ 1 := fun j t =>
    randomizedRecoveryFamily_contractions_norm_le s U E hn0 N j t
  have hcomm : ∀ j t, ‖(h * x j t - x j t * h) (F j t ξ)‖ ≤ δ * ‖F j t ξ‖ := by
    intro j t
    have hb' : ‖h * x j t - x j t * h‖ ≤ δ :=
      (hb _ (recoverySequenceContractions M N v j t).property).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hx j t) hδ)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hb' (norm_nonneg _))
  have hF : ∀ j, finiteRMS (fun t => F j t ξ) ≤ 1 := by
    intro j
    change finiteRMS (fun t =>
      recoverySequenceForwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t ξ) ≤ 1
    exact le_of_eq ((randomizedRecoveryFamily_forward_finiteRMS s U E hN hNq j ξ).trans hξ)
  have hG : ∀ j, finiteRMS (fun t => G j t ξ) ≤ 1 := by
    intro j
    change finiteRMS (fun t =>
      recoverySequenceBackwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t ξ) ≤ 1
    exact le_of_eq ((randomizedRecoveryFamily_backward_finiteRMS s U E hN hNq j ξ).trans hξ)
  obtain ⟨c, hc, hlim⟩ :=
    D.exists_randomizedRecoveryFamily_weak_scalar (q := q) (N := N) hτ hσ s hs U E hn hsize
  exact row_complex_scalar_quadratic_bound h hh T (diagonalAmplification_isSelfAdjoint h hh)
    u ξ F G x hδ hc hx hcomm hF hG hforward hbackward hlim

end

end KadisonKastler

end OAI
