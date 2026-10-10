import OAI.Analysis.KadisonKastler.AmplificationRowLimits
import OAI.Analysis.KadisonKastler.RandomizedQuadratic
import OAI.Analysis.KadisonKastler.RecoveryParameters

namespace OAI

/-! # The amplified unitary commutator estimate from a controlled free lift -/

namespace KadisonKastler

open Filter

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n : ℕ} [NeZero n]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {P : VonNeumannAlgebra K} {σ : FaithfulTracialState (Algebra P)} {ω : Ultrafilter ℕ}

local instance unitaryBoundSourceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance unitaryBoundSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance unitaryBoundOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance unitaryBoundOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance unitaryBoundMatrixOrder :
    PartialOrder (Algebra (matrixVonNeumann (ι := Fin n) M)) := CStarAlgebra.spectralOrder _
local instance unitaryBoundMatrixStarOrder :
    StarOrderedRing (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  CStarAlgebra.spectralOrderedRing _

/-- With a controlled free Haar representative, all finite random choices
can be made and eliminated. No row estimate is an assumption of this theorem. -/
theorem unitary_commutator_le_of_free_lift
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τ : FaithfulTracialState (Algebra M))
    (D : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
    (hτ : FiniteVectorTrace τ) (hσ : FiniteVectorTrace σ)
    (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (hFock : PublishedDiagonalFockRepresentation.{v})
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (hfree : FreeHaarMoments σ D.constant.range
      (Unitary.map (StarMonoidHom.ofClass D.quotient) s))
    (h : H →L[ℂ] H) (hh : h.IsSymmetric) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (hs : ∀ j, let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
        ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ)
    (hn : 2 ≤ n) (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M))) :
    let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
    ‖T * U.val.val - U.val.val * T‖ ≤ 282 * δ := by
  obtain ⟨N, q, hN, hq, hsize⟩ := exists_recovery_degrees n
  have hNq : N < q := by omega
  let : NeZero q := ⟨by omega⟩
  obtain ⟨k, hk, hNk, hE, hword, hthrough⟩ :=
    exists_amplification_partition_matrixUnits hM n N (by omega)
  let : NeZero k := ⟨by omega⟩
  let E := Classical.choice hE
  let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
  let u := Unitary.map (StarMonoidHom.ofClass
    (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype) U
  change ‖T * (u : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) -
    (u : Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) * T‖ ≤ 282 * δ
  apply norm_commutator_le_of_unit_quadratic T (diagonalAmplification_isSelfAdjoint h hh)
    u (by positivity)
  intro ξ hξ
  have hforward := randomized_recovery_forward_row_limit (q := q) (N := N) τ D E s U hτ hCyclic hFock
    hfree hN hNq hNk (fun r _ hr => hword r hr) hthrough h hδ hb hs ξ hξ
  have hbackward := randomized_recovery_backward_row_limit (q := q) (N := N) τ D E s U hτ hCyclic hFock
    hfree hN hNq hNk (fun r _ hr => hword r hr) hthrough h hδ hb ξ hξ
  exact randomized_recovery_quadratic_bound (q := q) (N := N) D hτ hσ s hfree U E h hh hδ hb hn hN hNq
    hsize ξ hξ hforward hbackward

end

end KadisonKastler

end OAI
