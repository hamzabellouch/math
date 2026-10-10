import Mathlib

namespace OAI

/-!
Finite union-bound lemmas for the independent random binary codebook argument
in polynomial-code.tex, Lemma `lem:random-segments`.
-/

namespace TreeEdit.BinaryLower
namespace CodeUnionBound

open scoped BigOperators

/-- A finite family whose total cardinality is smaller than the ambient type
cannot cover that type. No probability-space assumptions are required. -/
theorem exists_avoiding_of_sum_card_lt
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    (bad : I → Finset Ω)
    (h : (∑ i, (bad i).card) < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i : I, ω ∉ bad i := by
  classical
  by_contra hn
  push Not at hn
  have hcover : (Finset.univ : Finset Ω) ⊆ Finset.univ.biUnion bad := by
    intro ω _
    obtain ⟨i, hi⟩ := hn ω
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hc : Fintype.card Ω ≤ ∑ i, (bad i).card := by
    calc
      Fintype.card Ω = (Finset.univ : Finset Ω).card := by simp
      _ ≤ (Finset.univ.biUnion bad).card := Finset.card_le_card hcover
      _ ≤ ∑ i, (bad i).card := Finset.card_biUnion_le
  exact (not_lt_of_ge hc) h

/-- The same existence statement in terms of real-valued probability bounds
for the uniform distribution on a nonempty finite ambient type. -/
theorem exists_avoiding_of_probability_bounds
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (bad : I → Finset Ω) (p : I → ℝ)
    (hbound : ∀ i, ((bad i).card : ℝ) / Fintype.card Ω ≤ p i)
    (hsum : (∑ i, p i) < 1) :
    ∃ ω : Ω, ∀ i : I, ω ∉ bad i := by
  apply exists_avoiding_of_sum_card_lt bad
  have hpos : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hsum' : (∑ i, ((bad i).card : ℝ)) / Fintype.card Ω < 1 := by
    rw [Finset.sum_div]
    exact (Finset.sum_le_sum fun i _ => hbound i).trans_lt hsum
  have hc : (∑ i, ((bad i).card : ℝ)) < Fintype.card Ω := by
    simpa using (div_lt_iff₀ hpos).mp hsum'
  exact_mod_cast hc

/-- A uniform bad-event estimate needs only a bound on the number of events. -/
theorem exists_avoiding_of_uniform_probability_bound
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (bad : I → Finset Ω) (ε : ℝ)
    (hbound : ∀ i, ((bad i).card : ℝ) / Fintype.card Ω ≤ ε)
    (hsum : (Fintype.card I : ℝ) * ε < 1) :
    ∃ ω : Ω, ∀ i : I, ω ∉ bad i := by
  apply exists_avoiding_of_probability_bounds bad (fun _ => ε) hbound
  simpa using hsum

/-- The uniform criterion with a possibly loose real-valued upper bound on
the number of comparisons. This permits endpoints represented by `Fin (P+1)`
without changing the union-bound argument. -/
theorem exists_avoiding_of_event_count_bound
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (bad : I → Finset Ω) (ε N : ℝ) (hε : 0 ≤ ε)
    (hcount : (Fintype.card I : ℝ) ≤ N)
    (hbound : ∀ i, ((bad i).card : ℝ) / Fintype.card Ω ≤ ε)
    (hsum : N * ε < 1) :
    ∃ ω : Ω, ∀ i : I, ω ∉ bad i := by
  apply exists_avoiding_of_uniform_probability_bound bad ε hbound
  exact (mul_le_mul_of_nonneg_right hcount hε).trans_lt hsum

/-- There are at most `K² P³` ordered choices of two codeword labels,
a positive segment length at most `P`, and two starting positions. The
validity conditions only remove comparisons from this ambient index type. -/
abbrev SegmentComparison (K P : ℕ) :=
  Fin K × Fin K × Fin P × Fin P × Fin P

theorem card_segmentComparison (K P : ℕ) :
    Fintype.card (SegmentComparison K P) = K ^ 2 * P ^ 3 := by
  simp only [SegmentComparison, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The polynomial number of comparisons is dominated by the twentieth
power appearing after the source's logarithmic segment cutoff. -/
theorem comparison_frequency_lt_one {m p : ℝ}
    (hm : 2 ≤ m) (hp : 1 ≤ p) :
    m ^ 2 * p ^ 3 / (m * p) ^ 20 < 1 := by
  have hm0 : 0 ≤ m := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hmp : 1 < m * p := by nlinarith
  apply (div_lt_one (pow_pos (by linarith : 0 < m * p) 20)).2
  calc
    m ^ 2 * p ^ 3 ≤ m ^ 3 * p ^ 3 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by decide))
        (pow_nonneg hp0 3)
    _ = (m * p) ^ 3 := (mul_pow m p 3).symm
    _ < (m * p) ^ 20 := pow_lt_pow_right₀ hmp (by decide)

/-- A uniform matching-event bound produces one codebook satisfying
every segment comparison simultaneously. -/
theorem exists_codebook_avoiding
    {M K P : ℕ} (hM : 2 ≤ M) (hK : K ≤ M) (hP : 1 ≤ P)
    (bad : SegmentComparison K P → Finset ((Fin K × Fin P) → Bool))
    (hbound : ∀ i,
      ((bad i).card : ℝ) / (2 : ℝ) ^ (K * P) ≤
        1 / ((M : ℝ) * P) ^ 20) :
    ∃ c : (Fin K × Fin P) → Bool, ∀ i, c ∉ bad i := by
  classical
  apply exists_avoiding_of_uniform_probability_bound bad
    (1 / ((M : ℝ) * P) ^ 20)
  · intro i
    simpa only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat] using hbound i
  · rw [card_segmentComparison]
    push_cast
    have hKreal : (K : ℝ) ≤ M := by exact_mod_cast hK
    have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hPreal : (1 : ℝ) ≤ P := by exact_mod_cast hP
    have hden : 0 ≤ 1 / ((M : ℝ) * P) ^ 20 := by positivity
    calc
      (K : ℝ) ^ 2 * P ^ 3 * (1 / ((M : ℝ) * P) ^ 20) ≤
          (M : ℝ) ^ 2 * P ^ 3 * (1 / ((M : ℝ) * P) ^ 20) := by
        gcongr
      _ = (M : ℝ) ^ 2 * P ^ 3 / ((M : ℝ) * P) ^ 20 := by ring
      _ < 1 := comparison_frequency_lt_one hMreal hPreal

/-- The source cutoff converts each `2^(-a/2)` segment-failure estimate
into an inverse sixtieth power of the input length. -/
theorem exponential_bound_of_source_cutoff {m a : ℝ}
    (hm : 0 < m) (ha : 120 * Real.logb 2 m ≤ a) :
    Real.exp (-a * Real.log 2 / 2) ≤ 1 / m ^ 60 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscale : 120 * Real.log m ≤ a * Real.log 2 := by
    have h := (mul_le_mul_of_nonneg_right ha hlog2.le)
    simpa [Real.logb, div_mul_cancel₀ _ (ne_of_gt hlog2),
      mul_assoc] using h
  calc
    Real.exp (-a * Real.log 2 / 2) ≤ Real.exp (-(60 * Real.log m)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = 1 / m ^ 60 := by
      have hlog : Real.log (m ^ 60) = 60 * Real.log m := by
        simp [Real.log_pow]
      rw [← hlog]
      rw [Real.exp_neg, Real.exp_log (pow_pos hm 60)]
      simp only [one_div]

/-- The slightly larger `(P+1)^3` comparison index used by endpoint-based
formalizations still has total bad probability strictly below one. -/
theorem endpoint_comparison_frequency_lt_one {m : ℝ} (hm : 2 ≤ m) :
    m ^ 2 * (m ^ 2 + 1) ^ 3 / m ^ 60 < 1 := by
  have hm0 : 0 < m := by linarith
  have hm21 : 1 ≤ m ^ 2 := by nlinarith
  have h8 : (8 : ℝ) ≤ m ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm 3
    norm_num at h ⊢
    exact h
  apply (div_lt_one (pow_pos hm0 60)).2
  calc
    m ^ 2 * (m ^ 2 + 1) ^ 3 ≤ m ^ 2 * (2 * m ^ 2) ^ 3 := by
      gcongr
      linarith
    _ = 8 * m ^ 8 := by ring
    _ ≤ m ^ 3 * m ^ 8 := mul_le_mul_of_nonneg_right h8 (pow_nonneg hm0.le 8)
    _ = m ^ 11 := by ring
    _ < m ^ 60 := pow_lt_pow_right₀ (by linarith) (by decide)

/-- Final numerical union-bound estimate at the exact logarithmic cutoff,
with endpoint-based comparison indexing and `P=M²`. -/
theorem source_cutoff_total_probability_lt_one {m a : ℝ}
    (hm : 2 ≤ m) (ha : 120 * Real.logb 2 m ≤ a) :
    m ^ 2 * (m ^ 2 + 1) ^ 3 * Real.exp (-a * Real.log 2 / 2) < 1 := by
  calc
    m ^ 2 * (m ^ 2 + 1) ^ 3 * Real.exp (-a * Real.log 2 / 2) ≤
        m ^ 2 * (m ^ 2 + 1) ^ 3 * (1 / m ^ 60) := by
      apply mul_le_mul_of_nonneg_left
        (exponential_bound_of_source_cutoff (by linarith) ha)
      positivity
    _ = m ^ 2 * (m ^ 2 + 1) ^ 3 / m ^ 60 := by ring
    _ < 1 := endpoint_comparison_frequency_lt_one hm

end CodeUnionBound
end TreeEdit.BinaryLower

end OAI
