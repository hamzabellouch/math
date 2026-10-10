import OAI.NumberTheory.TotientAsymptotic.PPTPreimageSplit
import OAI.NumberTheory.TotientAsymptotic.PPTComparisonBridge
import OAI.NumberTheory.TotientAsymptotic.PPTCoordinateAlignment

namespace OAI

/-!
The unequal-list normality argument applied to an actual chosen preimage.
Its smooth factor is the totient of the low part of that preimage.  The
equation here is derived from the given totient identity, rather than
imposed as an additional comparison hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_actual_preimage_equation {k d n : ℕ} (p : Fin k → ℕ) {S : ℝ}
    (hn : 0 < n) (hS : 1 ≤ S)
    (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (hvalue : n.totient = d*(∏ i, p i).totient)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ r : ℕ, r.Prime → r ∣ n → IsNormalPrime S r) :
    ∃ (l : ℕ) (q : Fin l → ℕ) (E : ℕ),
      0 < E ∧ (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ S < (q i : ℝ)) ∧
      d*shiftedProduct p = E*shiftedProduct q := by
  obtain ⟨l, q, s, hs, _, _, hsS, hqanti, hq, hφ⟩ :=
    ppt_preimage_prime_split hn hS hsq hnormal
  refine ⟨l, q, s.totient, Nat.totient_pos.mpr hs, hsS, hqanti, hq, ?_⟩
  calc
    d*shiftedProduct p = d*(∏ i, p i).totient := by
      rw [ppt_totient_primeProduct p hp hpinj]
    _ = n.totient := hvalue.symm
    _ = s.totient*shiftedProduct q := hφ

/-- A sufficiently high actual left coordinate forces the corresponding
right prime to exist. No equality of the total list lengths is needed. -/
theorem ppt_actual_preimage_right_index {k d n : ℕ} (p : Fin k → ℕ)
    (j : Fin k) {S T ε : ℝ} (hd : 0 < d) (hn : 0 < n)
    (hS : 1 < S) (hBS : 0 ≤ B S)
    (hp : ∀ i, IsNormalPrime S (p i)) (hpa : StrictAnti p)
    (hvalue : n.totient = d*(∏ i, p i).totient)
    (hDS : (largestPrimeFactor d : ℝ) ≤ S)
    (hsq : SquarefreeAbove n S)
    (hnormal : ∀ r : ℕ, r.Prime → r ∣ n → IsNormalPrime S r)
    (hST : S < T) (hTp : T ≤ (p j-1 : ℕ))
    (hε : Real.sqrt (B S*B T) ≤ ε)
    (hgap : (2*(j.val : ℝ)+1)*ε < B T-B S) :
    ∃ (l : ℕ) (q : Fin l → ℕ) (E : ℕ),
      0 < E ∧ (largestPrimeFactor E : ℝ) ≤ S ∧ StrictAnti q ∧
      (∀ i, IsNormalPrime S (q i) ∧ S < (q i : ℝ)) ∧
      d*shiftedProduct p = E*shiftedProduct q ∧
      ∃ hj : j.val < l, S < (q ⟨j.val, hj⟩-1 : ℕ) := by
  obtain ⟨l, q, E, hE, hES, hqa, hq, heq⟩ :=
    ppt_actual_preimage_equation p hn hS.le (fun i => (hp i).1)
      hpa.injective hvalue hsq hnormal
  refine ⟨l, q, E, hE, hES, hqa, hq, heq, ?_⟩
  exact ppt_ordered_right_index p q j hS hBS hd.ne' hE.ne' hp (fun i => (hq i).1)
    hpa.antitone hqa.antitone heq hDS hES hST hTp hε hgap

end TotientAsymptotic

end

end OAI
