import OAI.Analysis.KadisonKastler.AmplificationPowerLimits
import OAI.Analysis.KadisonKastler.RecoveryRowDrift
import OAI.Analysis.KadisonKastler.RecoveryRandomizedFamily

namespace OAI

/-! # Actual randomized recovery rows have drift at most `70δ`

The finitely many power estimates are combined with scalar-phase orthogonality
and coordinate normalization.  The resulting statements concern precisely the
rows used in the scalar recovery average.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k q N : ℕ} [NeZero n] [NeZero k] [NeZero q]
local instance rowLimitSourceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance rowLimitSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowLimitOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance rowLimitOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowLimitMatrixOrder :
    PartialOrder (Algebra (matrixVonNeumann (ι := Fin n) M)) := CStarAlgebra.spectralOrder _
local instance rowLimitMatrixStarOrder :
    StarOrderedRing (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  CStarAlgebra.spectralOrderedRing _

variable {B : Type v} [CStarAlgebra B] {σ : FaithfulTracialState B} {ω : Ultrafilter ℕ}
variable (τ : FaithfulTracialState (Algebra M))
variable (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
variable (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
variable (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
variable (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M)))
variable (hτ : FiniteVectorTrace τ)
variable (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
variable (hFock : PublishedDiagonalFockRepresentation.{v})
variable (hfree : FreeHaarMoments σ R.constant.range
  (Unitary.map (StarMonoidHom.ofClass R.quotient) s))
variable (hN : 0 < N) (hNq : N < q) (hNk : N ≤ k)
variable (hword : ∀ r : ℕ, 1 ≤ r → r ≤ N → freeWordThreshold r ≤ n * k)
variable (hthrough : ∀ r : ℕ, 1 ≤ r → r ≤ N → ∀ a : Fin (n * k),
  (∑ t : ThroughLabel a r, projectionWordWeight (freeWordC r) t.val ^ 2) ≤ 64)
variable (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
variable (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)

include hτ hCyclic hFock hfree hN hNq hNk hword hthrough hδ hb in
/-- The actual forward recovery rows have eventual drift `70δ` on a unit vector. -/
theorem randomized_recovery_forward_row_limit
    (hs : ∀ j, let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
        ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ)
    (ξ : Generator.FiniteHilbert (Fin n) H) (hξ : ‖ξ‖ = 1) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      finiteRMS (fun t : ((Fin (n * k) → ZMod q) × ZMod q) × Fin n =>
        h (recoverySequenceForwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t ξ) -
          recoverySequenceForwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t
            ((star U.val.val) (T (U.val.val ξ)))) ≤ 70 * δ + ε := by
  let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
  let v := fun (j : ℕ) (θ : Fin (n * k) → ZMod q) =>
    phaseWordBase E (sequenceUnitaryEval s j * U) θ
  let ζ := (star U.val.val) (T (U.val.val ξ))
  have hpower : ∀ r : Fin N, ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      finiteRMS (fun θ =>
        T (((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val ξ) -
          ((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^ (r.val + 1)).val ζ) ≤
            70 * δ + ε := by
    intro r
    have hrN : r.val + 1 ≤ N := by omega
    simpa only [hξ, mul_one] using
      positive_amplification_power_limit τ R E s U hτ hCyclic hFock hfree
        r.val (hrN.trans hNk) (hrN.trans_lt hNq)
        (hword (r.val + 1) (by omega) hrN)
        (hthrough (r.val + 1) (by omega) hrN) h hδ hb hs ξ
  have hrows := eventually_recoveryForwardRows_drift_le (N := N) (q := q)
    M (ω : Filter ℕ) h T (diagonalAmplification_coordinate_compatibility h)
    v ξ ζ hN hNq hpower
  intro ε hε
  filter_upwards [hrows ε hε] with j hj
  simpa only [recoverySequenceForwardRows, randomizedRecoveryFamily,
    randomizedRecoveryLift_eval, v, phaseWordBase] using hj

include hτ hCyclic hFock hfree hN hNq hNk hword hthrough hδ hb in
/-- The adjoint recovery rows satisfy the matching actual `70δ` drift bound. -/
theorem randomized_recovery_backward_row_limit
    (ξ : Generator.FiniteHilbert (Fin n) H) (hξ : ‖ξ‖ = 1) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      finiteRMS (fun t : ((Fin (n * k) → ZMod q) × ZMod q) × Fin n =>
        h (recoverySequenceBackwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t ξ) -
          recoverySequenceBackwardRows M N (randomizedRecoveryFamily (q := q) s U E) j t
            (T ξ)) ≤ 70 * δ + ε := by
  let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
  let v := fun (j : ℕ) (θ : Fin (n * k) → ZMod q) =>
    phaseWordBase E (sequenceUnitaryEval s j * U) θ
  have hpower : ∀ r : Fin N, ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      finiteRMS (fun θ =>
        T ((star ((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
          (r.val + 1))).val ξ) -
        (star ((v j θ : Algebra (matrixVonNeumann (ι := Fin n) M)) ^
          (r.val + 1))).val (T ξ)) ≤ 70 * δ + ε := by
    intro r
    have hrN : r.val + 1 ≤ N := by omega
    simpa only [hξ, mul_one] using
      negative_amplification_power_limit τ R E s U hτ hCyclic hFock hfree
        r.val (hrN.trans hNk) (hrN.trans_lt hNq)
        (hword (r.val + 1) (by omega) hrN)
        (hthrough (r.val + 1) (by omega) hrN) h hδ hb ξ
  have hrows := eventually_recoveryBackwardRows_drift_le (N := N) (q := q)
    M (ω : Filter ℕ) h T (diagonalAmplification_coordinate_compatibility h)
    v ξ hN hNq hpower
  intro ε hε
  filter_upwards [hrows ε hε] with j hj
  simpa only [recoverySequenceBackwardRows, randomizedRecoveryFamily,
    randomizedRecoveryLift_eval, v, phaseWordBase] using hj

end

end KadisonKastler

end OAI
