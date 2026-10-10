import OAI.NumberTheory.Ostmann.Construction.IntegerIntervalCoordinates
import OAI.NumberTheory.Ostmann.Characters.SparsePairSizeBound

namespace OAI

/-! # Applying both sides of the sparse contraction to integer intervals -/
namespace Ostmann
open scoped Classical BigOperators

theorem integer_complementary_energy_budgets (ls : PublishedAdditiveLargeSieve)
    {n m M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (hSp : ∀ i, (S i).card < p i)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hcover : ∀ q, q.Prime → q ≤ Q → ∃ i, p i = q)
    (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) (J J' : ℤ)
    (hArange : ∀ a ∈ A, J ≤ a ∧ a < J + M)
    (hBrange : ∀ b ∈ B, J' ≤ b ∧ b < J' + M)
    (ha : ∀ x ∈ A, ∀ i, (x : ZMod (p i)) ∈ S i)
    (hb : ∀ y ∈ B, ∀ i, (y : ZMod (p i)) ∈ Finset.univ \ S i)
    (e : Fin m ↪ Fin n) (K : ℕ)
    (hprod : ∀ T : Finset (Fin m), T.card ≤ K → (∏ i ∈ T, p (e i)) ≤ Q)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ K →
      (∑ q ∈ T.image (fun i => p (e i)), (q : ℝ)⁻¹) ≤ 1 / 16)
    (R : ℝ) (hR : 0 < R)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ R / 16) :
    let α := (Q : ℝ) / 16 * Real.exp (-R)
    let D := (M : ℝ) + (Q : ℝ) ^ 2
    (α * countingVectorNorm (lowModeVector K (averagedCoordinates A
        (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤ D / A.card) ∧
    (α * countingVectorNorm (lowModeVector K (averagedCoordinates B
        (fun x => tensorPointCoordinates (fun i => p (e i))
          (fun i => Finset.univ \ S (e i))
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤ D / B.card) := by
  constructor
  · exact restricted_integer_energy_budget ls p hc S hS κ hκ hκS hQ hM hcover
      A hA J hArange ha e K hprod hsmall R hR hP
  · have hSc (i : Fin n) : (Finset.univ \ S i).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card]
      exact Nat.sub_pos_of_lt (hSp i)
    have hκSc (i : Fin n) : (κ (p i))⁻¹ = (p i : ℝ) / (Finset.univ \ S i).card - 1 := by
      rw [hκS]
      exact complementary_field_card_ratio (S i) (hS i) (hSp i)
    have hPinv : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)⁻¹| / q) ≤ R / 16 := by
      simpa only [Real.log_inv, abs_neg] using hP
    exact restricted_integer_energy_budget ls p hc (fun i => Finset.univ \ S i)
      hSc (fun q => (κ q)⁻¹) (fun q hq => inv_pos.mpr (hκ q hq))
      hκSc hQ hM hcover B hB J' hBrange hb e K hprod hsmall R hR hPinv

end Ostmann

end OAI
