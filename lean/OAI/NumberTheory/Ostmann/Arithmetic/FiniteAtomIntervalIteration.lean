import OAI.NumberTheory.Ostmann.Arithmetic.FiniteAtomIntervalStep
import OAI.NumberTheory.Ostmann.Arithmetic.FiniteArithmeticIteration

namespace OAI

/-! # Finite-depth iteration with whole-word interval support -/
namespace Ostmann
open scoped BigOperators Classical

theorem scheduled_constituent_atom_interval_step {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (j : ℕ) (hpivot : ∀ k ≤ j, role (pivot k).1 = .pivot k) (p : I) (hp : role p = .pivot j) (hu : ∀ i, role i = .pivot j → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (lo hi : I → ℕ) (cellLo cellHi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i)
    (V pivotBound : ℕ → ℕ) (hV : Monotone V)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (hpLo : 0 < lo p) (hpHi : hi p ≤ pivotBound j)
    (hcellLo : lo p ≤ ∏ t : Fin (size p), cellLo ⟨p, t⟩)
    (hcellHi : (∏ t : Fin (size p), cellHi ⟨p, t⟩) ≤ hi p)
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hgap : 2 * pivotBound j * V j <
      ∏ h : CopyScheduleH role j, lo (copyScheduleOrigin j h.val))
    (hscale : 2 * V j *
      (∏ h : CopyScheduleH role j, hi (copyScheduleOrigin j h.val))
        ≤ V (j + 1) * lo p)
    (hlarge : ∀ q ∈ P, V (j + 1) < q)
    (loss : ℝ) (hcost : (((size p).factorial : ℝ) *
      ∏ i : Fin (size p), (∑ q ∈ Q ⟨p, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp loss) :
    Real.exp (-loss) * ‖scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi
      V pivotBound leaf center j‖ ^ 2 ≤
      scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi V pivotBound leaf center p j +
        ‖scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi V pivotBound leaf center (j + 1)‖ := by
  apply constituentPrimeGuardedAmplitude_atom_interval_step role size χ κ pivot j hpivot p hp hu P hP Q
    hκ hQP hQ lo hi cellLo cellHi hcell V pivotBound leaf (scheduledFrequencyHistory V j)
    center _ (V (j + 1)) hpLo hpHi hcellLo hcellHi
  · exact scheduledFrequencyHistory_root_bound V j
  · exact hzero
  · intro d s hs q hq
    exact (scheduledFrequencyHistory_all_bound V hV j d s hs).trans_lt
      ((hV (Nat.le_succ j)).trans_lt (hlarge q hq))
  · exact le_rfl
  · exact hgap
  · exact hscale
  · exact hlarge
  · exact hcost

/-- The initial reserve survives every actual arithmetic step once the
explicit diagonals and the sum of the actual losses have been bounded. -/
theorem scheduled_constituent_atom_interval_iteration {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (k : ℕ) (hpivot : ∀ j < k, role (pivot j).1 = .pivot j) (p : ℕ → I)
    (hp : ∀ j < k, role (p j) = .pivot j)
    (hu : ∀ j < k, ∀ i, role i = .pivot j → i = p j)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (lo hi : I → ℕ) (cellLo cellHi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i)
    (V pivotBound : ℕ → ℕ) (hV : Monotone V)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)
    (hpLo : ∀ j < k, 0 < lo (p j))
    (hpHi : ∀ j < k, hi (p j) ≤ pivotBound j)
    (hcellLo : ∀ j < k, lo (p j) ≤ ∏ t : Fin (size (p j)), cellLo ⟨p j, t⟩)
    (hcellHi : ∀ j < k, (∏ t : Fin (size (p j)), cellHi ⟨p j, t⟩) ≤ hi (p j))
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hgap : ∀ j < k, 2 * pivotBound j * V j <
      ∏ h : CopyScheduleH role j, lo (copyScheduleOrigin j h.val))
    (hscale : ∀ j < k, 2 * V j *
      (∏ h : CopyScheduleH role j, hi (copyScheduleOrigin j h.val))
        ≤ V (j + 1) * lo (p j))
    (hlarge : ∀ q ∈ P, V k < q)
    (loss : ℕ → ℝ) (hloss : ∀ j < k, 0 ≤ loss j)
    (hcost : ∀ j < k, (((size (p j)).factorial : ℝ) *
      ∏ i : Fin (size (p j)), (∑ q ∈ Q ⟨p j, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp (loss j))
    (B₀ m : ℝ) (hm : 0 ≤ m)
    (hbudget : ∑ j ∈ Finset.range k, (loss j + Real.log 2) ≤ m)
    (hinit : Real.exp (-B₀ * m) ≤
      ‖scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi V pivotBound leaf center 0‖)
    (hdiag : ∀ j < k, scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi
      V pivotBound leaf center (p j) j ≤
        Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ j * m)) :
    Real.exp (-(B₀ + 1) * (2 : ℝ) ^ k * m) ≤
      ‖scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi V pivotBound leaf center k‖ := by
  apply variable_transfer_iteration k
    (scheduledConstituentAmplitude role size χ κ pivot P hP Q lo hi V pivotBound leaf center)
    (fun j => scheduledConstituentDiagonal role size χ κ pivot P hP Q lo hi
      V pivotBound leaf center (p j) j) loss B₀ m hm hloss hbudget hinit hdiag
    (fun j hj => ?_) k le_rfl
  exact scheduled_constituent_atom_interval_step role size χ κ pivot j
    (fun t ht => hpivot t (by omega)) (p j) (hp j hj)
    (hu j hj) P hP Q hκ hQP hQ lo hi cellLo cellHi hcell V pivotBound hV leaf center
    (hpLo j hj) (hpHi j hj) (hcellLo j hj) (hcellHi j hj) hzero (hgap j hj) (hscale j hj)
    (fun q hq => (hV (by omega : j + 1 ≤ k)).trans_lt (hlarge q hq)) (loss j) (hcost j hj)

end Ostmann

end OAI
