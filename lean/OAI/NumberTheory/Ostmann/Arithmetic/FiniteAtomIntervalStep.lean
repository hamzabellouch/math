import OAI.NumberTheory.Ostmann.Arithmetic.FiniteArithmeticStep
import OAI.NumberTheory.Ostmann.Construction.ConstituentAtomProductBounds

namespace OAI

/-! # Finite transfer using the selected whole-word intervals -/
namespace Ostmann
open scoped Classical BigOperators

theorem constituentPrimeGuardedAmplitude_atom_interval_step {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (hpivot : ∀ k ≤ n, role (pivot k).1 = .pivot k) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (lo hi : I → ℕ) (cellLo cellHi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hist : D → FrequencyTree ℤ n) (center : ∀ p : ℕ, ZMod p) (K V : ℕ)
    (hpLo : 0 < lo p) (hpHi : hi p ≤ pivotBound n)
    (hcellLo : lo p ≤ ∏ k : Fin (size p), cellLo ⟨p, k⟩)
    (hcellHi : (∏ k : Fin (size p), cellHi ⟨p, k⟩) ≤ hi p)
    (hroot : ∀ d, (frequencyRoot n (hist d)).natAbs ≤ childBound n)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d s, s ∈ allFrequencyList n (hist d) → ∀ q ∈ P, s.natAbs < q)
    (hK : (∏ h : CopyScheduleH role n, hi (copyScheduleOrigin n h.val)) ≤ K)
    (hgap : 2 * pivotBound n * childBound n <
      ∏ h : CopyScheduleH role n, lo (copyScheduleOrigin n h.val))
    (hscale : 2 * childBound n * K ≤ V * lo p) (hlarge : ∀ q ∈ P, V < q)
    (loss : ℝ) (hcost : (((size p).factorial : ℝ) *
      ∏ i : Fin (size p), (∑ q ∈ Q ⟨p, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp loss) :
    Real.exp (-loss) *
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
        childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center‖ ^ 2 ≤
      (∑ u, (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
        ∑ M ∈ Finset.Icc (lo p) (hi p), (constituentPivotDiagonal role size χ κ pivot n P hP Q
          childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center u M).re) +
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
        childBound pivotBound (atomIntervalRanges role lo hi) leaf (copiedConstituentHistory hist V) center‖ := by
  apply constituentPrimeGuardedAmplitude_step_finite role size χ κ pivot n hpivot p hp hu P hP Q
    hκ hQP hQ childBound pivotBound (atomIntervalRanges role lo hi) leaf hist center K V
    (Finset.Icc (lo p) (hi p))
  · intro x _ hx
    apply Finset.mem_Icc.mpr
    exact ⟨hcellLo.trans (Finset.prod_le_prod (fun i _ => (hcell _ _ (hx i)).1)),
      (Finset.prod_le_prod (fun i _ => (hcell _ _ (hx i)).2)).trans hcellHi⟩
  · exact hzero
  · exact hsmall
  · intro M hM
    exact hpLo.trans_le (Finset.mem_Icc.mp hM).1
  · intro M hM
    exact (Finset.mem_Icc.mp hM).2.trans hpHi
  · intro u l d M _ _ hw
    exact Finset.mem_Icc.mpr (fullAtomTransferWeight_inserted_pivot_bounds role lo hi
      childBound pivotBound leaf n p hp M _ _ (hist d) hw)
  · intro u M _ a ha
    have hh := constituentTransferWeight_atom_product_bounds role size n P Q childBound pivotBound
      lo hi leaf hist u M a ha
    exact ⟨hroot a.2, hh.2.trans hK⟩
  · intro M hM
    exact hscale.trans (Nat.mul_le_mul_left V (Finset.mem_Icc.mp hM).1)
  · exact hlarge
  · intro u M _ a b _ hb
    have hh := constituentTransferWeight_atom_product_bounds role size n P Q childBound pivotBound
      lo hi leaf hist u M b hb
    exact hgap.trans_le hh.1
  · intro u M _ a b ha hb
    exact constituentTransferWeight_copied_intervals role size lo hi n P Q childBound pivotBound
      leaf hist u M a b ha hb
  · exact hcost

end Ostmann

end OAI
