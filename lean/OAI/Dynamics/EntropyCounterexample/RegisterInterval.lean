import OAI.Dynamics.EntropyCounterexample.RegisterLinearity

namespace OAI

noncomputable section

namespace Problem340.Register

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem delayed_register_linearity_Ico
    (L : ℝ) (hL : 1 ≤ L) (s j : ℕ) (hsj : s ≤ j)
    (c : ℕ → E) (S : E → E) (v : ℕ → E)
    (hc : (∑ i ∈ Finset.Ico s j, ‖c i‖) ≤ (1 / 2 : ℝ))
    (hS : ∀ x : E, ‖x‖ ≤ 1 → S x = x)
    (hvs : v s = 0)
    (hstep : ∀ n, s ≤ n → n < j → v (n + 1) = L • S (v n) +
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n) :
    (∀ n, s ≤ n → n ≤ j →
      v n = L ^ ((n : ℤ) - (j : ℤ)) • ∑ i ∈ Finset.Ico s n, c i ∧
      ‖v n‖ ≤ (1 / 2 : ℝ)) ∧
    v j = ∑ i ∈ Finset.Ico s j, c i := by
  have hc' : (∑ i ∈ Finset.range (j - s), ‖c (s + i)‖) ≤ (1 / 2 : ℝ) := by
    simpa [Finset.sum_Ico_eq_sum_range, Nat.add_comm] using hc
  have hstep' : ∀ n < j - s,
      v (s + (n + 1)) = L • S (v (s + n)) +
        L ^ ((n : ℤ) + 1 - ((j - s : ℕ) : ℤ)) • c (s + n) := by
    intro n hn
    have he : (((s + n : ℕ) : ℤ) + 1 - (j : ℤ)) =
        ((n : ℤ) + 1 - ((j - s : ℕ) : ℤ)) := by omega
    simpa only [Nat.add_assoc, he] using hstep (s + n) (by omega) (by omega)
  have h := delayed_register_linearity L hL (j - s) (fun n => c (s + n)) S
    (fun n => v (s + n)) hc' hS (by simpa using hvs) hstep'
  have hmain : ∀ n, s ≤ n → n ≤ j →
      v n = L ^ ((n : ℤ) - (j : ℤ)) • ∑ i ∈ Finset.Ico s n, c i ∧
        ‖v n‖ ≤ (1 / 2 : ℝ) := by
    intro n hsn hnj
    have hn : n - s ≤ j - s := by omega
    have he : (((n - s : ℕ) : ℤ) - ((j - s : ℕ) : ℤ)) =
        ((n : ℤ) - (j : ℤ)) := by omega
    have hn' : s + (n - s) = n := Nat.add_sub_of_le hsn
    obtain ⟨hvalue, hnorm⟩ := h.1 (n - s) hn
    refine ⟨?_, ?_⟩
    · simpa only [hn', delayedCandidate, he, Finset.sum_Ico_eq_sum_range,
        Nat.add_comm] using hvalue
    · simpa only [hn'] using hnorm
  refine ⟨hmain, ?_⟩
  simpa using (hmain j hsj le_rfl).1

theorem delayed_register_readout_finite
    (L : ℝ) (hL : 1 ≤ L) (s j : ℕ) (hsj : s ≤ j)
    (c : ℕ → E) (S : E → E) (v : ℕ → E)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico s j) (hcard : I.card ≤ 5)
    (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ))
    (hsupport : ∀ i ∈ Finset.Ico s j, i ∉ I → c i = 0)
    (hS : ∀ x : E, ‖x‖ ≤ 1 → S x = x)
    (hvs : v s = 0)
    (hstep : ∀ n, s ≤ n → n < j → v (n + 1) = L • S (v n) +
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n) :
    (∀ n, s ≤ n → n ≤ j → ‖v n‖ ≤ (1 / 2 : ℝ)) ∧
      v j = ∑ i ∈ I, c i ∧ S (v j) = v j := by
  have hnormsum : (∑ i ∈ I, ‖c i‖) = ∑ i ∈ Finset.Ico s j, ‖c i‖ := by
    apply Finset.sum_subset hI
    intro i hi hnot
    simp [hsupport i hi hnot]
  have hsum : (∑ i ∈ I, c i) = ∑ i ∈ Finset.Ico s j, c i :=
    Finset.sum_subset hI hsupport
  have htotal : (∑ i ∈ Finset.Ico s j, ‖c i‖) ≤ (1 / 2 : ℝ) := by
    rw [← hnormsum]
    exact coefficient_norm_sum_le_half I c hcard hc
  obtain ⟨hstates, hread⟩ := delayed_register_linearity_Ico L hL s j hsj c S v
    htotal hS hvs hstep
  refine ⟨fun n hsn hnj => (hstates n hsn hnj).2, hread.trans hsum.symm, ?_⟩
  exact hS (v j) (le_trans (hstates j hsj le_rfl).2 (by norm_num))

theorem register_readout_of_identified_inputs
    (L : ℝ) (hL : 1 ≤ L) (s j : ℕ) (hsj : s ≤ j)
    (a : ℕ → ℝ) (input c v : ℕ → E) (S : E → E)
    (hrec : ∀ n, v (n + 1) = a n • S (v n) + input n)
    (hgain : ∀ n, s ≤ n → n < j → a n = L)
    (hinput : ∀ n, s ≤ n → n < j → input n =
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico s j) (hcard : I.card ≤ 5)
    (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ))
    (hsupport : ∀ i ∈ Finset.Ico s j, i ∉ I → c i = 0)
    (hS : ∀ x : E, ‖x‖ ≤ 1 → S x = x) (hvs : v s = 0) :
    (∀ n, s ≤ n → n ≤ j → ‖v n‖ ≤ (1 / 2 : ℝ)) ∧
      v j = ∑ i ∈ I, c i ∧ S (v j) = v j := by
  apply delayed_register_readout_finite L hL s j hsj c S v I hI hcard hc hsupport hS hvs
  intro n hsn hnj
  rw [hrec n, hgain n hsn hnj, hinput n hsn hnj]

end Problem340.Register

end

end OAI
