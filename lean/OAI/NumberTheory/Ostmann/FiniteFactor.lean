import OAI.NumberTheory.Ostmann.Endpoint
import OAI.NumberTheory.Ostmann.FiniteCRT

namespace OAI

namespace Ostmann
open scoped Pointwise symmDiff

theorem finite_factor_impossible (A B : Set ℕ) (hfin : A.Finite)
    (hA : A.Nontrivial) : ¬ EventuallyEqual (A+B) primes := by
  classical
  intro h
  obtain ⟨N, hexclude, hcover⟩ := (eventual_sumset_iff A B).mp h
  obtain ⟨a₀, ha₀, a₁, ha₁, hdistinct⟩ := hA
  let f : ℕ → ℕ := fun a => if a = a₀ then a₁ else a₀
  have hf : ∀ a, f a ∈ A := by
    intro a
    dsimp [f]
    split_ifs
    · exact ha₁
    · exact ha₀
  have hne : ∀ a, a ≠ f a := by
    intro a
    dsimp [f]
    split_ifs with heq
    · simpa only [heq] using hdistinct
    · exact heq
  obtain ⟨M, hM⟩ := hfin.bddAbove
  let t := hfin.toFinset
  have ht : ∀ a, a ∈ t ↔ a ∈ A := fun a => hfin.mem_toFinset
  obtain ⟨Q, r, hQ, hr, hres⟩ := exists_reduced_class t f M
    (fun a ha => hM ((ht a).mp ha))
    (fun a _ => hM (hf a)) (fun a _ => hne a)
  let K := t.sup (separatingPrime M)
  obtain ⟨p, hpbound, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (N+M+K) hQ hr
  obtain ⟨a, ha, b, hb, hab⟩ := hcover p (by omega) hp
  have hat : a ∈ t := (ht a).mpr ha
  have ham : a ≤ M := hM ha
  have haq : separatingPrime M a ≤ K := Finset.le_sup (f := separatingPrime M) hat
  have hbgt : N+K < b := by omega
  obtain ⟨hares, haQ⟩ := hres a hat
  have hpa : p ≡ separatingPrime M a + a - f a [MOD separatingPrime M a] :=
    (hpmod.of_dvd haQ).trans hares
  have hfa : f a ≤ separatingPrime M a + a :=
    (hM (hf a)).trans (Nat.le_add_right_of_le (lt_separatingPrime M a).le)
  have hshift := hpa.add_right (f a)
  rw [Nat.sub_add_cancel hfa] at hshift
  have he : p + f a = a + (f a+b) := by omega
  rw [he] at hshift
  have hqzero : separatingPrime M a + a ≡ a + 0 [MOD separatingPrime M a] := by
    simp [Nat.ModEq]
  have hd : separatingPrime M a ∣ f a+b := Nat.modEq_zero_iff_dvd.mp
    (Nat.ModEq.add_left_cancel' a (hshift.trans hqzero))
  have hp' : (f a+b).Prime := hexclude (f a) (hf a) b hb (by omega)
  have heq := (Nat.prime_dvd_prime_iff_eq (separatingPrime_prime M a) hp').mp hd
  omega

theorem finite_factor_infinite_disagreement (A B : Set ℕ)
    (hfin : A.Finite) (hA : A.Nontrivial) : ((A+B) ∆ primes).Infinite :=
  (infinite_symmDiff_iff_not_eventuallyEqual _ _).mpr
    (finite_factor_impossible A B hfin hA)

end Ostmann

end OAI
