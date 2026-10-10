import OAI.NumberTheory.Ostmann.Construction.WordTransferGuardFamily

namespace OAI

/-! # The full small-frequency modulus, including every node's unit tests -/

namespace Ostmann

open scoped Classical

def allFrequencyList : (n : ℕ) → FrequencyTree ℤ n → List ℤ
  | 0, t => [t]
  | n + 1, t => t.1 :: (allFrequencyList n t.2.1 ++ allFrequencyList n t.2.2)

theorem frequencyRoot_mem_allFrequencyList (n : ℕ) (t : FrequencyTree ℤ n) :
    frequencyRoot n t ∈ allFrequencyList n t := by
  cases n <;> simp [allFrequencyList, frequencyRoot]

theorem internalFrequencyList_subset_all (n : ℕ) (t : FrequencyTree ℤ n) :
    ∀ s ∈ internalFrequencyList n t, s ∈ allFrequencyList n t := by
  induction n with
  | zero => simp [internalFrequencyList]
  | succ n ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact List.mem_cons_self ..
    · rcases List.mem_append.mp hs with hs | hs
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih _ s hs))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih _ s hs))

theorem allFrequencyList_length (n : ℕ) (t : FrequencyTree ℤ n) :
    (allFrequencyList n t).length = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allFrequencyList, List.length_cons, List.length_append, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem WordTransferTemplate.guards_frequencies_mem {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ template.guards t hn env,
      g.root ∈ allFrequencyList n t ∧ g.right ∈ allFrequencyList n t := by
  induction template generalizing env with
  | leaf word => simp [guards]
  | @node n d l r hl hr =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _
        (List.mem_append_right _ (frequencyRoot_mem_allFrequencyList n t.2.2))⟩
    · rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨hs, hw⟩ := hl _ _ _ g hg
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_left _ hs),
          List.mem_cons_of_mem _ (List.mem_append_left _ hw)⟩
      · obtain ⟨hs, hw⟩ := hr _ _ _ g hg
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ hs),
          List.mem_cons_of_mem _ (List.mem_append_right _ hw)⟩

def wordTransferFullPeriod (n : ℕ) (t : FrequencyTree ℤ n) (B : ℕ) : ℕ :=
  historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) *
    historyFrequencyBase (allFrequencyList n t)

theorem wordTransferFullPeriod_pos (n : ℕ) (t : FrequencyTree ℤ n) (B : ℕ)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) : 0 < wordTransferFullPeriod n t B := by
  exact Nat.mul_pos (historyFrequencyPeriod_pos _ _
    (fun s hs => hz s (internalFrequencyList_subset_all n t s hs)))
    (historyFrequencyBase_pos _ hz)

/-- Both units at every original node are periodic in this explicitly
constructed modulus, including units modulo leaf frequencies. -/
theorem WordTransferTemplate.guards_full_period {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) :
    ∀ g ∈ template.guards t hn .prime,
      g.pivot.cleared.denominator * g.right.natAbs ∣ (wordTransferFullPeriod n t B : ℤ) ∧
      g.rightProduct.cleared.denominator * g.root.natAbs ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro g hg
  have hd := template.guards_denominator_period t hn B hB hwords 1 (one_dvd _) g hg
  simp only [mul_one] at hd
  have hf := template.guards_frequencies_mem t hn .prime g hg
  have hmod (s : ℤ) (hs : s ∈ allFrequencyList n t) :
      (s.natAbs : ℤ) ∣ (historyFrequencyBase (allFrequencyList n t) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Int.dvd_natCast.mp (frequency_dvd_historyFrequencyBase _ s hs))
  constructor
  · simpa only [wordTransferFullPeriod, Nat.cast_mul] using mul_dvd_mul hd.1 (hmod _ hf.2)
  · simpa only [wordTransferFullPeriod, Nat.cast_mul] using mul_dvd_mul hd.2 (hmod _ hf.1)

theorem wordTransferFullPeriod_le (n : ℕ) (t : FrequencyTree ℤ n) (B V : ℕ)
    (hV : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) :
    wordTransferFullPeriod n t B ≤
      V ^ ((2 ^ n - 1) * (B ^ (n + 1) + 1) + (2 ^ (n + 1) - 1)) := by
  have hi := historyFrequencyPeriod_le (internalFrequencyList n t) V (B ^ (n + 1) + 1)
    (fun s hs => hV s (internalFrequencyList_subset_all n t s hs))
  have ha := historyFrequencyPeriod_le (allFrequencyList n t) V 1 hV
  simp only [historyFrequencyPeriod, pow_one, mul_one] at ha
  rw [internalFrequencyList_length] at hi
  rw [allFrequencyList_length] at ha
  exact (Nat.mul_le_mul hi ha).trans_eq (pow_add _ _ _).symm

theorem prime_coprime_wordTransferFullPeriod (n : ℕ) (t : FrequencyTree ℤ n) (B p : ℕ)
    (hp : p.Prime) (hsmall : ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p) :
    p.Coprime (wordTransferFullPeriod n t B) := by
  have hi := prime_coprime_historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) p hp
    (fun s hs => hsmall s (internalFrequencyList_subset_all n t s hs))
  have ha := prime_coprime_historyFrequencyPeriod (allFrequencyList n t) 1 p hp hsmall
  simp only [historyFrequencyPeriod, pow_one] at ha
  exact hi.mul_right ha

end Ostmann

end OAI
