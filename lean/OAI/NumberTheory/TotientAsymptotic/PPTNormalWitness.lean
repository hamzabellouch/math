import OAI.NumberTheory.TotientAsymptotic.PPTBadWitness
import OAI.NumberTheory.TotientAsymptotic.PPTSeedNormality

namespace OAI

/-!
The finite singleton-fiber reduction in Ford's exclusion (vi).  If the
candidate primes and the fixed seed primes are normal, a chosen preimage
with a nonnormal prime can only come from a singleton candidate-totient
fiber.  The exceptional candidates therefore give distinct target
totients, retaining the multiplicities elsewhere in the construction.
-/

noncomputable section

namespace TotientAsymptotic

/-- A nonnormal chosen preimage cannot lie in the seed-multiple branch of
the injective witness construction. -/
theorem ppt_nonnormal_witness_totient_injective {S Q : Finset ℕ}
    {F : ℕ → ℕ} {q : ℕ} {W : ℝ} (hQS : Q ⊆ S)
    (hS : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime W p)
    (hq : ∀ p : ℕ, p.Prime → p ∣ q → IsNormalPrime W p)
    (hbranch : ∀ n ∈ S,
      (∃ m ∈ S, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ S, F n = c*q)
    (hbad : ∀ n ∈ Q, ∃ p : ℕ, p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime W p) :
    Set.InjOn Nat.totient (Q : Set ℕ) := by
  intro n hn m hm he
  by_contra hne
  obtain ⟨c, hc, hF⟩ := hbranch n (hQS hn)
    ⟨m, hQS hm, Ne.symm hne, he.symm⟩
  obtain ⟨p, hp, hpd, hpn⟩ := hbad n hn
  rw [hF] at hpd
  rcases hp.dvd_mul.mp hpd with hpc | hpq
  · exact hpn (hS c hc p hp hpc)
  · exact hpn (hq p hp hpq)

/-- The corresponding seed-scaled target totients are distinct as well. -/
theorem ppt_nonnormal_witness_target_injective {S Q : Finset ℕ}
    {F : ℕ → ℕ} {d q : ℕ} {W : ℝ} (hd : 0 < d) (hQS : Q ⊆ S)
    (hS : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime W p)
    (hq : ∀ p : ℕ, p.Prime → p ∣ q → IsNormalPrime W p)
    (hbranch : ∀ n ∈ S,
      (∃ m ∈ S, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ S, F n = c*q)
    (hbad : ∀ n ∈ Q, ∃ p : ℕ, p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime W p) :
    Set.InjOn (fun n : ℕ => d*n.totient) (Q : Set ℕ) := by
  intro n hn m hm he
  exact ppt_nonnormal_witness_totient_injective hQS hS hq hbranch hbad hn hm
    (Nat.eq_of_mul_eq_mul_left hd he)

/-- Counting nonnormal chosen preimages reduces to counting their actual
distinct target totients.  The analytic exceptional-value estimate is a
separate input to this finite reduction. -/
theorem ppt_nonnormal_witness_count {S Q T : Finset ℕ}
    {F : ℕ → ℕ} {d q : ℕ} {W : ℝ} (hd : 0 < d) (hQS : Q ⊆ S)
    (hS : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime W p)
    (hq : ∀ p : ℕ, p.Prime → p ∣ q → IsNormalPrime W p)
    (hbranch : ∀ n ∈ S,
      (∃ m ∈ S, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ S, F n = c*q)
    (hbad : ∀ n ∈ Q, ∃ p : ℕ, p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime W p)
    (hT : ∀ n ∈ Q, d*n.totient ∈ T) :
    Q.card ≤ T.card := by
  classical
  have hinj := ppt_nonnormal_witness_target_injective hd hQS hS hq hbranch hbad
  have hsub : Q.image (fun n : ℕ => d*n.totient) ⊆ T := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    exact hT n hn
  calc
    Q.card = (Q.image (fun n : ℕ => d*n.totient)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ T.card := Finset.card_le_card hsub

end TotientAsymptotic

end

end OAI
