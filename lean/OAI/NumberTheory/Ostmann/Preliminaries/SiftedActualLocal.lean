import OAI.NumberTheory.Ostmann.Preliminaries.SiftedLocal

namespace OAI

namespace Ostmann.SiftedWeights
open Finset

theorem actual_local_energy_lower (d : Ostmann.Decomposition) (s : Finset ℕ) (K : ℕ)
    (hcard : s.card ≤ K) (hs : ∀ b ∈ s, b ∈ d.B) (hshift : ∀ b ∈ s, b ≤ K)
    {Q q : ℕ} [NeZero q] (hqs : Squarefree q) (hqQ : q ≤ Q)
    (hprimes : ∀ p ∈ q.primeFactors, K < p)
    (U : Finset ℕ) (hU : U.Nonempty)
    (hUA : ∀ a ∈ U, a ∈ d.A) (hlarge : ∀ a ∈ U, Q+d.cutoff < a) :
    (∏ p ∈ q.primeFactors, (s.card : ℝ)/((p : ℝ)-s.card)) ≤
      ∑ u : (ZMod q)ˣ, ‖normalizedExpSum U (((u : ZMod q).val : ℝ)/q)‖^2 := by
  classical
  let : ∀ p : q.primeFactors, NeZero (p : ℕ) := fun p =>
    ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  let S : ∀ p : q.primeFactors, Finset (ZMod (p : ℕ)) := fun p => allowedResidues s p
  have hpb : ∀ p : q.primeFactors, ∀ b ∈ s, b < (p : ℕ) :=
    fun p b hb => (hshift b hb).trans_lt (hprimes p p.property)
  have hpc : ∀ p : q.primeFactors, s.card < (p : ℕ) :=
    fun p => hcard.trans_lt (hprimes p p.property)
  have hSn : ∀ p, (S p).Nonempty :=
    fun p => allowedResidues_nonempty s (hpb p) (hpc p)
  have hS : ∀ a ∈ U, ∀ p, (a : ZMod (p : ℕ)) ∈ S p := by
    intro a ha p
    have hpQ : (p : ℕ) ≤ Q :=
      (Nat.le_of_dvd (NeZero.pos q) (Nat.dvd_of_mem_primeFactors p.property)).trans hqQ
    exact actual_mem_allowedResidues d s hs (Nat.prime_of_mem_primeFactors p.property)
      (hUA a ha) (by have := hlarge a ha; omega)
  have ht := local_product_le_primitive_energy hqs U hU S hSn hS
  have hprod : (∏ p : q.primeFactors, Supply.complementRatio (S p)) =
      ∏ p ∈ q.primeFactors, (s.card : ℝ)/((p : ℝ)-s.card) := by
    calc
      (∏ p : q.primeFactors, Supply.complementRatio (S p)) =
          ∏ p : q.primeFactors, (s.card : ℝ)/(((p : ℕ) : ℝ)-s.card) := by
        apply Finset.prod_congr rfl
        intro p _
        exact allowedResidues_factor s (hpb p) (hpc p)
      _ = _ := Finset.prod_coe_sort q.primeFactors
        (fun p : ℕ => (s.card : ℝ)/((p : ℝ)-s.card))
  rwa [hprod] at ht

end Ostmann.SiftedWeights

end OAI
