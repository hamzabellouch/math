import OAI.NumberTheory.DukePrimeDegree.Geometry.WeylDiagonalAction

namespace OAI

/-! # Periodicity of one diagonal map under full diagonal ergodicity

The chosen map need not itself be ergodic.  Its period-n fixed sets are
invariant under every diagonal translation, hence each has measure zero
or one.  There is either a common positive period almost everywhere or
almost every point has no positive period.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem diagonal_periodicity_dichotomy (d : ℕ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ] :
    (∃ n : ℕ, 0 < n ∧ ∀ᵐ x ∂μ,
      (fun y => rightAction y (diagonalOneParameter ell hell t))^[n] x = x) ∨
    (∀ᵐ x ∂μ, ∀ n : ℕ, 0 < n →
      (fun y => rightAction y (diagonalOneParameter ell hell t))^[n] x ≠ x) := by
  let T : X (d + 1) → X (d + 1) :=
    fun x => rightAction x (diagonalOneParameter ell hell t)
  have hcomm (u : Multiplicative (LogCoordinates d)) :
      Function.Commute T (fun x => u • x) := by
    intro x
    change rightAction (rightAction x (diagonalFlow u.toAdd))
      (diagonalOneParameter ell hell t) =
        rightAction (rightAction x (diagonalOneParameter ell hell t)) (diagonalFlow u.toAdd)
    rw [rightAction_mul, rightAction_mul]
    congr 1
    apply Subtype.ext
    exact (Matrix.commute_diagonal _ _).eq
  have hzeroone (n : ℕ) :
      (∀ᵐ x ∂μ, T^[n] x = x) ∨ (∀ᵐ x ∂μ, T^[n] x ≠ x) := by
    let E : Set (X (d + 1)) := {x | T^[n] x = x}
    have hE : MeasurableSet E :=
      (isClosed_eq ((continuous_rightAction _).iterate n) continuous_id).measurableSet
    have he : EventuallyEmptyOrUniv E (ae μ) :=
      ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
      (G := Multiplicative (LogCoordinates d)) (α := X (d + 1)) (μ := μ) hE (by
        intro u
        apply Filter.Eventually.of_forall
        intro x
        change (T^[n] (u • x) = u • x) = (T^[n] x = x)
        apply propext
        rw [(hcomm u).iterate_left n x]
        exact (MulAction.injective u).eq_iff)
    exact eventuallyEmptyOrUniv_iff.mp he
  by_cases hp : ∃ n : ℕ, 0 < n ∧ ∀ᵐ x ∂μ, T^[n] x = x
  · exact Or.inl hp
  · right
    apply ae_all_iff.mpr
    intro n
    by_cases hn : 0 < n
    · rcases hzeroone n with hyes | hno
      · exact (hp ⟨n, hn, hyes⟩).elim
      · exact hno.mono (fun _ hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ hx => (hn hx).elim)

end DukePrimeDegree

end

end OAI
