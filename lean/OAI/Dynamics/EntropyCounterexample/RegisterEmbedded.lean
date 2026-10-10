import OAI.Dynamics.EntropyCounterexample.RegisterLinearity

namespace OAI

noncomputable section

namespace Problem340.Register

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem embedded_delayed_register_linearity
    (L : ℝ) (hL : 1 ≤ L) (j : ℕ) (c : ℕ → E)
    (embed : E → X) (S : X → E) (v : ℕ → X)
    (hc : (∑ i ∈ Finset.range j, ‖c i‖) ≤ (1 / 2 : ℝ))
    (hS : ∀ z : E, ‖z‖ ≤ 1 → S (embed z) = z)
    (hv0 : v 0 = embed 0)
    (hstep : ∀ n < j, v (n + 1) = embed (L • S (v n) +
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n)) :
    (∀ n ≤ j, v n = embed (delayedCandidate L j c n)) ∧
      v j = embed (∑ i ∈ Finset.range j, c i) ∧
      S (v j) = ∑ i ∈ Finset.range j, c i ∧
      ‖S (v j)‖ ≤ (1 / 2 : ℝ) := by
  have hL0 : L ≠ 0 := by linarith
  have hmain : ∀ n ≤ j, v n = embed (delayedCandidate L j c n) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa using hv0
    | succ n ih =>
        intro hn
        have hn' : n ≤ j := by omega
        have hsmall : ‖delayedCandidate L j c n‖ ≤ 1 :=
          (norm_delayedCandidate_le L hL j c hc hn').trans (by norm_num)
        rw [hstep n (by omega), ih hn', hS _ hsmall]
        exact congrArg embed (delayedCandidate_succ L hL0 j c n).symm
  have hread : v j = embed (∑ i ∈ Finset.range j, c i) := by
    simpa using hmain j le_rfl
  have hbound : ‖∑ i ∈ Finset.range j, c i‖ ≤ (1 / 2 : ℝ) := by
    simpa using norm_delayedCandidate_le L hL j c hc (n := j) le_rfl
  have hsat : S (v j) = ∑ i ∈ Finset.range j, c i := by
    rw [hread]
    exact hS _ (hbound.trans (by norm_num))
  exact ⟨hmain, hread, hsat, hsat ▸ hbound⟩

theorem embedded_delayed_register_linearity_Ico
    (L : ℝ) (hL : 1 ≤ L) (s j : ℕ) (hsj : s ≤ j) (c : ℕ → E)
    (embed : E → X) (S : X → E) (v : ℕ → X)
    (hc : (∑ i ∈ Finset.Ico s j, ‖c i‖) ≤ (1 / 2 : ℝ))
    (hS : ∀ z : E, ‖z‖ ≤ 1 → S (embed z) = z)
    (hvs : v s = embed 0)
    (hstep : ∀ n, s ≤ n → n < j → v (n + 1) = embed (L • S (v n) +
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n)) :
    (∀ n, s ≤ n → n ≤ j → v n = embed
      (L ^ ((n : ℤ) - (j : ℤ)) • ∑ i ∈ Finset.Ico s n, c i)) ∧
      v j = embed (∑ i ∈ Finset.Ico s j, c i) ∧
      S (v j) = ∑ i ∈ Finset.Ico s j, c i ∧
      ‖S (v j)‖ ≤ (1 / 2 : ℝ) := by
  have hc' : (∑ i ∈ Finset.range (j - s), ‖c (s + i)‖) ≤ (1 / 2 : ℝ) := by
    simpa [Finset.sum_Ico_eq_sum_range, Nat.add_comm] using hc
  have hstep' : ∀ n < j - s,
      v (s + (n + 1)) = embed (L • S (v (s + n)) +
        L ^ ((n : ℤ) + 1 - ((j - s : ℕ) : ℤ)) • c (s + n)) := by
    intro n hn
    have he : (((s + n : ℕ) : ℤ) + 1 - (j : ℤ)) =
        ((n : ℤ) + 1 - ((j - s : ℕ) : ℤ)) := by omega
    simpa only [Nat.add_assoc, he] using hstep (s + n) (by omega) (by omega)
  obtain ⟨hmain, hread, hsat, hbound⟩ := embedded_delayed_register_linearity L hL
    (j - s) (fun n => c (s + n)) embed S (fun n => v (s + n)) hc' hS
    (by simpa using hvs) hstep'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hsn hnj
    have hn : n - s ≤ j - s := by omega
    have he : (((n - s : ℕ) : ℤ) - ((j - s : ℕ) : ℤ)) =
        ((n : ℤ) - (j : ℤ)) := by omega
    have hn' : s + (n - s) = n := Nat.add_sub_of_le hsn
    simpa only [hn', delayedCandidate, he, Finset.sum_Ico_eq_sum_range,
        Nat.add_comm] using hmain (n - s) hn
  · simpa [Nat.add_sub_of_le hsj, Finset.sum_Ico_eq_sum_range, Nat.add_comm] using hread
  · simpa [Nat.add_sub_of_le hsj, Finset.sum_Ico_eq_sum_range, Nat.add_comm] using hsat
  · simpa [Nat.add_sub_of_le hsj] using hbound

theorem embedded_register_readout_of_identified_inputs
    (L : ℝ) (hL : 1 ≤ L) (s j : ℕ) (hsj : s ≤ j)
    (a : ℕ → ℝ) (input c : ℕ → E) (v : ℕ → X)
    (embed : E → X) (S : X → E)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + input n))
    (hgain : ∀ n, s ≤ n → n < j → a n = L)
    (hinput : ∀ n, s ≤ n → n < j → input n =
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico s j) (hcard : I.card ≤ 5)
    (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ))
    (hsupport : ∀ i ∈ Finset.Ico s j, i ∉ I → c i = 0)
    (hS : ∀ z : E, ‖z‖ ≤ 1 → S (embed z) = z) (hvs : v s = embed 0) :
    (∀ n, s ≤ n → n ≤ j → v n = embed
      (L ^ ((n : ℤ) - (j : ℤ)) • ∑ i ∈ Finset.Ico s n, c i)) ∧
      v j = embed (∑ i ∈ I, c i) ∧
      S (v j) = ∑ i ∈ I, c i ∧ ‖S (v j)‖ ≤ (1 / 2 : ℝ) := by
  have hnormsum : (∑ i ∈ I, ‖c i‖) = ∑ i ∈ Finset.Ico s j, ‖c i‖ := by
    apply Finset.sum_subset hI
    intro i hi hnot
    simp [hsupport i hi hnot]
  have hsum : (∑ i ∈ I, c i) = ∑ i ∈ Finset.Ico s j, c i :=
    Finset.sum_subset hI hsupport
  have htotal : (∑ i ∈ Finset.Ico s j, ‖c i‖) ≤ (1 / 2 : ℝ) := by
    rw [← hnormsum]
    exact coefficient_norm_sum_le_half I c hcard hc
  have hstep : ∀ n, s ≤ n → n < j → v (n + 1) =
      embed (L • S (v n) + L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n) := by
    intro n hsn hnj
    rw [hrec n, hgain n hsn hnj, hinput n hsn hnj]
  obtain ⟨hmain, hread, hsat, hbound⟩ := embedded_delayed_register_linearity_Ico L hL
    s j hsj c embed S v htotal hS hvs hstep
  exact ⟨hmain, hread.trans (congrArg embed hsum.symm), hsat.trans hsum.symm, hbound⟩

end Problem340.Register

end

end OAI
