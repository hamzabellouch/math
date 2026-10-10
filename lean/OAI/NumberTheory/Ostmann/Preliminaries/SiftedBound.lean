import OAI.NumberTheory.Ostmann.Preliminaries.SiftedActualLocal
import OAI.NumberTheory.Ostmann.Preliminaries.SiftedEnergy
import OAI.NumberTheory.Ostmann.Preliminaries.SiftedModuli

namespace OAI

open Erdos970

namespace Ostmann.SiftedWeights
open Finset

theorem exists_finite_shift_sieve (d : Ostmann.Decomposition) (j : ℕ) :
    ∃ K : ℕ, ∃ C : ℝ, j ≤ K ∧ 0 < C ∧
      ∀ N Q : ℕ, max K 2 ≤ N → 1 < Q →
      (j : ℝ)*(Real.log (N : ℝ)+(Real.log 4+4)) ≤ Real.log (Q : ℝ)/2 →
      ∀ U : Finset ℕ, (∀ a ∈ U, a ∈ d.A) →
        (∀ a ∈ U, Q+d.cutoff < a) → (∀ a ∈ U, a ≤ Q^2) →
        (U.card : ℝ) ≤ C*(Q : ℝ)^2/(Real.log (N : ℝ))^j := by
  classical
  obtain ⟨s, K, hcard, hjK, hs, hshift⟩ := exists_shift_data d j
  have hsK : ∀ b ∈ s, b ≤ K := by
    intro b hb
    have := hshift (K+1) (Nat.lt_succ_self K) b hb
    omega
  obtain ⟨c, hc, hweight⟩ := sieveModuli_weight_lower j K hjK
  refine ⟨K, 96/c, hjK, by positivity, ?_⟩
  intro N Q hN hQ hmean U hUA hlarge hUsq
  have hn2 : 2 ≤ N := (le_max_right K 2).trans hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpow : 0 < (Real.log (N : ℝ))^j := pow_pos hlog j
  by_cases hUn : U.Nonempty
  · let M := sieveModuli (primeWindow K N) Q
    have hMP : ∀ q ∈ M, 0 < q ∧ q ≤ Q ∧ Squarefree q ∧ q.primeFactors ⊆ primeWindow K N :=
      fun q hq => mem_sieveModuli (fun p hp => (mem_primeWindow.mp hp).1) hq
    let : ∀ q : M, NeZero (q : ℕ) := fun q => ⟨(hMP q q.property).1.ne'⟩
    have hlocal : ∀ q : M,
        (∏ p ∈ (q : ℕ).primeFactors, (j : ℝ)/((p : ℝ)-j)) ≤
          ∑ u : (ZMod (q : ℕ))ˣ,
            ‖normalizedExpSum U (((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ))‖^2 := by
      intro q
      have hm := hMP q q.property
      have hh := actual_local_energy_lower d s K (by omega) hs hsK hm.2.2.1 hm.2.1
        (fun p hp => (mem_primeWindow.mp (hm.2.2.2 hp)).2.1) U hUn hUA hlarge
      simpa only [hcard] using hh
    have hsum := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset M)) => hlocal q)
    have hlow : c*(Real.log (N : ℝ))^j ≤
        ∑ q : M, ∏ p ∈ (q : ℕ).primeFactors, (j : ℝ)/((p : ℝ)-j) := by
      calc
        c*(Real.log (N : ℝ))^j ≤ ∑ q ∈ M, ∏ p ∈ q.primeFactors,
            (j : ℝ)/((p : ℝ)-j) := hweight N Q hN hQ hmean
        _ = ∑ q : M, ∏ p ∈ (q : ℕ).primeFactors, (j : ℝ)/((p : ℝ)-j) :=
          (Finset.sum_coe_sort M (fun q : ℕ =>
            ∏ p ∈ q.primeFactors, (j : ℝ)/((p : ℝ)-j))).symm
    have hsieve := primitive_energy_sum_le (fun q : M => (q : ℕ))
      (fun q => (hMP q q.property).2.1) Subtype.val_injective U hUsq (by omega)
    have hfull := hlow.trans (hsum.trans hsieve)
    have huc : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hUn
    have hmul := (le_div_iff₀ huc).mp hfull
    apply (le_div_iff₀ hpow).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith
  · have hu : U.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hUn)
    rw [hu, Nat.cast_zero]
    positivity

end Ostmann.SiftedWeights

end OAI
