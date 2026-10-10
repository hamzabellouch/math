import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.IndependentBlockSelection

/-- Number of block choices in which every block belongs to one bad set. -/
theorem card_all_bad_vectors {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset Ω) (R : ℕ) :
    (Finset.univ.filter (fun f : Fin R → Ω => ∀ i, f i ∈ B)).card = B.card ^ R := by
  classical
  calc
    (Finset.univ.filter (fun f : Fin R → Ω => ∀ i, f i ∈ B)).card =
        Fintype.card {f : Fin R → Ω // ∀ i, f i ∈ B} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card (Fin R → B) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = B.card ^ R := by simp

/-- A finite independent-block union bound with an explicit successful outcome.
    No probability or independence hypothesis is hidden: the sample space is
    exactly the Cartesian power `Fin R → Ω`. -/
theorem exists_blocks_of_bad_card_sum_lt {Ω U : Type*} [Fintype Ω]
    (s : Finset U) (B : U → Finset Ω) (R : ℕ)
    (hsmall : (∑ u ∈ s, (B u).card ^ R) < Fintype.card Ω ^ R) :
    ∃ f : Fin R → Ω, ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  classical
  let bad : U → Finset (Fin R → Ω) := fun u =>
    Finset.univ.filter (fun f => ∀ i, f i ∈ B u)
  have hcard : (s.biUnion bad).card < (Finset.univ : Finset (Fin R → Ω)).card := by
    calc
      (s.biUnion bad).card ≤ ∑ u ∈ s, (bad u).card := Finset.card_biUnion_le
      _ = ∑ u ∈ s, (B u).card ^ R := by
        apply Finset.sum_congr rfl
        intro u hu
        exact card_all_bad_vectors (B u) R
      _ < Fintype.card Ω ^ R := hsmall
      _ = (Finset.univ : Finset (Fin R → Ω)).card := by simp
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨f, ?_⟩
  intro u hu
  by_contra h
  push Not at h
  apply hf
  exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ f, h⟩⟩

/-- Real-valued probability form, allowing distinct error budgets for each item. -/
theorem exists_blocks_of_probability_sum_lt {Ω U : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Finset U) (B : U → Finset Ω) (R : ℕ) (p : U → ℝ)
    (hbad : ∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤ p u)
    (hsmall : (∑ u ∈ s, p u ^ R) < 1) :
    ∃ f : Fin R → Ω, ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  apply exists_blocks_of_bad_card_sum_lt s B R
  have hΩ : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (Fintype.card Ω : ℝ) ^ R := pow_pos hΩ R
  have hsum : (∑ u ∈ s, ((B u).card : ℝ) ^ R) /
      (Fintype.card Ω : ℝ) ^ R < 1 := by
    calc
      (∑ u ∈ s, ((B u).card : ℝ) ^ R) / (Fintype.card Ω : ℝ) ^ R =
          ∑ u ∈ s, (((B u).card : ℝ) / Fintype.card Ω) ^ R := by
        simp only [div_pow, Finset.sum_div]
      _ ≤ ∑ u ∈ s, p u ^ R := by
        apply Finset.sum_le_sum
        intro u hu
        exact pow_le_pow_left₀ (by positivity) (hbad u hu) R
      _ < 1 := hsmall
  have hreal : (∑ u ∈ s, ((B u).card : ℝ) ^ R) <
      (Fintype.card Ω : ℝ) ^ R := (div_lt_one hpow).mp hsum
  exact_mod_cast hreal

/-- Summability gives a uniform bound for every finite set beyond one cutoff. -/
theorem finite_tail_sum_lt_of_summable (f : ℕ → ℝ) (hf : Summable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, (∀ u ∈ s, N ≤ u) → (∑ u ∈ s, f u) < ε := by
  obtain ⟨t, ht⟩ := hf.vanishing (Iio_mem_nhds hε)
  refine ⟨t.sup id + 1, ?_⟩
  intro s hs
  apply ht s
  apply Finset.disjoint_left.mpr
  intro u hus hut
  have hu : u ≤ t.sup id := Finset.le_sup (f := id) hut
  have hv := hs u hus
  omega

/-- The terminal error `u⁻⁵` is uniformly summable over arbitrary finite ranges. -/
theorem finite_inverse_fifth_tail_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, (∀ u ∈ s, N ≤ u) →
      (∑ u ∈ s, (1 : ℝ) / (u : ℝ) ^ 5) < ε := by
  apply finite_tail_sum_lt_of_summable _ _ hε
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

/-- Uniform terminal-level selection from an inverse-fifth-power block error. -/
theorem exists_terminal_blocks :
    ∃ N : ℕ, ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (s : Finset ℕ) (B : ℕ → Finset Ω) (R : ℕ) (p : ℕ → ℝ),
      (∀ u ∈ s, N ≤ u) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤ p u) →
      (∀ u ∈ s, p u ^ R ≤ (1 : ℝ) / (u : ℝ) ^ 5) →
      ∃ f : Fin R → Ω, ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  obtain ⟨N, hN⟩ := finite_inverse_fifth_tail_lt (show (0 : ℝ) < 1 by norm_num)
  refine ⟨N, ?_⟩
  intro Ω _ _ s B R p hs hbad herr
  apply exists_blocks_of_probability_sum_lt s B R p hbad
  exact (Finset.sum_le_sum herr).trans_lt (hN s hs)

/-- Joint selection avoiding a global exceptional event and all local failures. -/
theorem exists_blocks_avoiding_global_bad_of_card_sum_lt
    {Ω U : Type*} [Fintype Ω] (s : Finset U) (B : U → Finset Ω)
    (R : ℕ) (E : Finset (Fin R → Ω))
    (hsmall : E.card + (∑ u ∈ s, (B u).card ^ R) < Fintype.card Ω ^ R) :
    ∃ f : Fin R → Ω, f ∉ E ∧ ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  classical
  let bad : U → Finset (Fin R → Ω) := fun u =>
    Finset.univ.filter (fun f => ∀ i, f i ∈ B u)
  have hcard : (E ∪ s.biUnion bad).card <
      (Finset.univ : Finset (Fin R → Ω)).card := by
    calc
      (E ∪ s.biUnion bad).card ≤ E.card + (s.biUnion bad).card :=
        Finset.card_union_le _ _
      _ ≤ E.card + ∑ u ∈ s, (bad u).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
      _ = E.card + ∑ u ∈ s, (B u).card ^ R := by
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        exact card_all_bad_vectors (B u) R
      _ < Fintype.card Ω ^ R := hsmall
      _ = (Finset.univ : Finset (Fin R → Ω)).card := by simp
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨f, fun h => hf (Finset.mem_union_left _ h), ?_⟩
  intro u hu
  by_contra h
  push Not at h
  apply hf
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ f, h⟩⟩

/-- Probability budgets add even when the global event is not independent
    of any of the individual terminal events. -/
theorem exists_blocks_avoiding_global_bad_of_probability_sum_lt
    {Ω U : Type*} [Fintype Ω] [Nonempty Ω] (s : Finset U)
    (B : U → Finset Ω) (R : ℕ) (E : Finset (Fin R → Ω)) (p : U → ℝ)
    (hbad : ∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤ p u)
    (hsmall : (E.card : ℝ) / (Fintype.card Ω : ℝ) ^ R +
      (∑ u ∈ s, p u ^ R) < 1) :
    ∃ f : Fin R → Ω, f ∉ E ∧ ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  apply exists_blocks_avoiding_global_bad_of_card_sum_lt s B R E
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (Fintype.card Ω : ℝ) ^ R := pow_pos hΩ R
  have hsum : ((E.card : ℝ) + ∑ u ∈ s, ((B u).card : ℝ) ^ R) /
      (Fintype.card Ω : ℝ) ^ R < 1 := by
    calc
      ((E.card : ℝ) + ∑ u ∈ s, ((B u).card : ℝ) ^ R) /
          (Fintype.card Ω : ℝ) ^ R =
          (E.card : ℝ) / (Fintype.card Ω : ℝ) ^ R +
          ∑ u ∈ s, (((B u).card : ℝ) / Fintype.card Ω) ^ R := by
        simp only [add_div, div_pow, Finset.sum_div]
      _ ≤ (E.card : ℝ) / (Fintype.card Ω : ℝ) ^ R + ∑ u ∈ s, p u ^ R := by
        apply add_le_add (le_refl _)
        apply Finset.sum_le_sum
        intro u hu
        exact pow_le_pow_left₀ (by positivity) (hbad u hu) R
      _ < 1 := hsmall
  have hreal := (div_lt_one hpow).mp hsum
  exact_mod_cast hreal

/-- Final simultaneous-selection form: a global budget below one leaves room
    for every sufficiently far-out finite collection of terminal integers. -/
theorem exists_terminal_blocks_with_global_bad (δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (s : Finset ℕ) (B : ℕ → Finset Ω) (R : ℕ)
      (E : Finset (Fin R → Ω)) (p : ℕ → ℝ),
      (∀ u ∈ s, N ≤ u) →
      ((E.card : ℝ) / (Fintype.card Ω : ℝ) ^ R ≤ δ) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤ p u) →
      (∀ u ∈ s, p u ^ R ≤ (1 : ℝ) / (u : ℝ) ^ 5) →
      ∃ f : Fin R → Ω, f ∉ E ∧ ∀ u ∈ s, ∃ i : Fin R, f i ∉ B u := by
  obtain ⟨N, hN⟩ := finite_inverse_fifth_tail_lt (sub_pos.mpr hδ)
  refine ⟨N, ?_⟩
  intro Ω _ _ s B R E p hs hE hbad herr
  apply exists_blocks_avoiding_global_bad_of_probability_sum_lt s B R E p hbad
  have htail := (Finset.sum_le_sum herr).trans_lt (hN s hs)
  linarith

/-- One thousand blocks turn `u^(-.005)`
    into the summable error `u^(-5)`. -/
theorem thousand_blocks_rpow (u : ℕ) :
    ((u : ℝ) ^ (-(1 / 200 : ℝ))) ^ 1000 = (1 : ℝ) / (u : ℝ) ^ 5 := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg u)]
  norm_num

/-- Explicit 1000-block form of simultaneous terminal selection. -/
theorem exists_thousand_terminal_blocks_with_global_bad (δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (s : Finset ℕ) (B : ℕ → Finset Ω) (E : Finset (Fin 1000 → Ω)),
      (∀ u ∈ s, N ≤ u) →
      ((E.card : ℝ) / (Fintype.card Ω : ℝ) ^ 1000 ≤ δ) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤
        (u : ℝ) ^ (-(1 / 200 : ℝ))) →
      ∃ f : Fin 1000 → Ω, f ∉ E ∧ ∀ u ∈ s, ∃ i : Fin 1000, f i ∉ B u := by
  obtain ⟨N, hN⟩ := exists_terminal_blocks_with_global_bad δ hδ
  refine ⟨N, ?_⟩
  intro Ω _ _ s B E hs hE hbad
  exact hN Ω s B 1000 E (fun u => (u : ℝ) ^ (-(1 / 200 : ℝ)))
    hs hE hbad (fun u _ => (thousand_blocks_rpow u).le)

/-- Restricting the first block has exactly its single-block failure fraction. -/
theorem card_bad_first_block {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset Ω) (R : ℕ) :
    (Finset.univ.filter (fun f : Fin (R + 1) → Ω => f 0 ∈ B)).card =
      B.card * Fintype.card Ω ^ R := by
  classical
  let e : {f : Fin (R + 1) → Ω // f 0 ∈ B} ≃ B × (Fin R → Ω) :=
    { toFun := fun f => (⟨f.1 0, f.2⟩, Fin.tail f.1)
      invFun := fun p => ⟨Fin.cons p.1.1 p.2, p.1.2⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      right_inv := by
        intro p
        rcases p with ⟨b, f⟩
        rfl }
  calc
    (Finset.univ.filter (fun f : Fin (R + 1) → Ω => f 0 ∈ B)).card =
        Fintype.card {f : Fin (R + 1) → Ω // f 0 ∈ B} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card (B × (Fin R → Ω)) := Fintype.card_congr e
    _ = B.card * Fintype.card Ω ^ R := by simp

/-- Normalized first-block bad count, for combining a middle-level event
    on block zero with terminal success on at least one of all blocks. -/
theorem bad_first_block_fraction {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (B : Finset Ω) (R : ℕ) :
    ((Finset.univ.filter (fun f : Fin (R + 1) → Ω => f 0 ∈ B)).card : ℝ) /
        (Fintype.card Ω : ℝ) ^ (R + 1) = (B.card : ℝ) / Fintype.card Ω := by
  rw [card_bad_first_block]
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Ω))
  push_cast
  rw [pow_succ]
  field_simp

/-- A realization with a good middle-level block and a successful block for
    every terminal integer, matching the final simultaneous selection step. -/
theorem exists_middle_and_terminal_blocks (δ : ℝ) (hδ : δ < 1) :
    ∃ N : ℕ, ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (s : Finset ℕ) (B : ℕ → Finset Ω) (middleBad : Finset Ω),
      (∀ u ∈ s, N ≤ u) →
      ((middleBad.card : ℝ) / Fintype.card Ω ≤ δ) →
      (∀ u ∈ s, ((B u).card : ℝ) / Fintype.card Ω ≤
        (u : ℝ) ^ (-(1 / 200 : ℝ))) →
      ∃ f : Fin 1000 → Ω, f 0 ∉ middleBad ∧
        ∀ u ∈ s, ∃ i : Fin 1000, f i ∉ B u := by
  classical
  obtain ⟨N, hN⟩ := exists_thousand_terminal_blocks_with_global_bad δ hδ
  refine ⟨N, ?_⟩
  intro Ω _ _ s B middleBad hs hmiddle hbad
  let E : Finset (Fin 1000 → Ω) :=
    Finset.univ.filter (fun f => f 0 ∈ middleBad)
  have hE : (E.card : ℝ) / (Fintype.card Ω : ℝ) ^ 1000 ≤ δ := by
    exact (bad_first_block_fraction middleBad 999).trans_le hmiddle
  obtain ⟨f, hf, hterminal⟩ := hN Ω s B E hs hE hbad
  refine ⟨f, ?_, hterminal⟩
  simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hf

end Problem337.IndependentBlockSelection

end

end OAI
