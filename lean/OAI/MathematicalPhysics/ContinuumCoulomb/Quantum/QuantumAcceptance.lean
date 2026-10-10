import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGates
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockBlocks

namespace OAI

/-! Zero-ancilla witness inclusion and the actual Born probability bounds. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix HubbardGlobal
open scoped BigOperators

/-- A witness basis vector with every ancillary qubit set to zero. -/
def qmaWitnessBasis (c : QMACircuit) (s : SourceSpinBasis c.witness) :
    SourceSpinBasis (c.work + 1) :=
  fun i => if hi : i.val < c.witness then s ⟨i.val, hi⟩ else 0

/-- Restriction to the witness register of a well-formed circuit. -/
def qmaWitnessPrefix (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis (c.work + 1)) : SourceSpinBasis c.witness :=
  fun i => s ⟨i.val, lt_of_lt_of_le i.isLt (hc.1.trans (Nat.le_succ _))⟩

@[simp] theorem qmaWitnessPrefix_basis (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis c.witness) : qmaWitnessPrefix c hc (qmaWitnessBasis c s) = s := by
  funext i
  simp [qmaWitnessPrefix, qmaWitnessBasis, i.isLt]

theorem qmaWitnessBasis_injective (c : QMACircuit) (hc : c.WellFormed) :
    Function.Injective (qmaWitnessBasis c) :=
  Function.LeftInverse.injective (qmaWitnessPrefix_basis c hc)

theorem qmaWitnessBasis_prefix (c : QMACircuit) (hc : c.WellFormed)
    (s : SourceSpinBasis (c.work + 1))
    (hs : ∀ i : Fin (c.work + 1), c.witness ≤ i.val → s i = 0) :
    qmaWitnessBasis c (qmaWitnessPrefix c hc s) = s := by
  funext i
  by_cases hi : i.val < c.witness
  · simp [qmaWitnessBasis, qmaWitnessPrefix, hi]
  · simp [qmaWitnessBasis, hi, hs i (Nat.le_of_not_gt hi)]

/-- The initial-state definition is the concrete coordinate inclusion of the
witness subspace, and therefore applies to arbitrary entangled witnesses. -/
theorem qmaInitialState_eq_inclusion (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    WithLp.toLp 2 (qmaInitialState c hc psi) = coordinateInclusion (qmaWitnessBasis c) psi := by
  classical
  ext s
  by_cases hs : ∀ i : Fin (c.work + 1), c.witness ≤ i.val → s i = 0
  · have heq := qmaWitnessBasis_prefix c hc s hs
    rw [← heq, coordinateInclusion_apply_image _ (qmaWitnessBasis_injective c hc)]
    change qmaInitialState c hc psi (qmaWitnessBasis c (qmaWitnessPrefix c hc s)) =
      psi (qmaWitnessPrefix c hc s)
    rw [heq, qmaInitialState, ite_eq_left hs]
    rfl
  · rw [coordinateInclusion_apply_outside]
    · simp [qmaInitialState, hs]
    · intro a ha
      apply hs
      intro i hi
      rw [← ha]
      simp [qmaWitnessBasis, Nat.not_lt.mpr hi]

theorem qmaInitialState_norm (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    ‖WithLp.toLp 2 (qmaInitialState c hc psi)‖ = ‖psi‖ := by
  rw [qmaInitialState_eq_inclusion]
  exact coordinateInclusion_norm_map _ (qmaWitnessBasis_injective c hc) psi

/-- The complete output distribution has exactly the witness norm squared. -/
theorem qmaOutput_total (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    (∑ s, Complex.normSq ((qmaCircuitMatrix c).mulVec (qmaInitialState c hc psi) s)) =
      ‖psi‖ ^ 2 := by
  let initial : EuclideanSpace ℂ (SourceSpinBasis (c.work + 1)) :=
    WithLp.toLp 2 (qmaInitialState c hc psi)
  have hnorm := qmaCircuit_preserves_norm c hc initial
  rw [qmaInitialState_norm c hc psi] at hnorm
  rw [← hnorm, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro s _
  rw [Complex.normSq_eq_norm_sq]
  rfl

theorem qmaAcceptance_nonneg (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    0 ≤ qmaAcceptance c hc psi := by
  unfold qmaAcceptance
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

theorem qmaAcceptance_le_norm_sq (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance c hc psi ≤ ‖psi‖ ^ 2 := by
  rw [← qmaOutput_total c hc psi]
  apply Finset.sum_le_sum
  intro s _
  split_ifs
  · exact le_rfl
  · exact Complex.normSq_nonneg _

/-- A normalized witness produces an actual probability in the unit interval. -/
theorem qmaAcceptance_mem_unitInterval (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1) :
    qmaAcceptance c hc psi ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨qmaAcceptance_nonneg c hc psi, ?_⟩
  simpa only [hpsi, one_pow] using qmaAcceptance_le_norm_sq c hc psi

end ContinuumCoulomb

end

end OAI
