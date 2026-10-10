import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedProgram

namespace OAI

/-! Removing already fixed source answers is a proof operation on a
query. It preserves the table trace and separates source/table charges;
the implementation continues to cache and sample explicit source keys. -/

namespace EditApproximation.FiniteQuery

variable {σ κ : Type*}

def eraseSources (sourceAnswer : σ → ℚ) : FiniteQuery (Sum σ κ) → FiniteQuery κ
  | .done value => .done value
  | .read (.inl source) next => eraseSources sourceAnswer (next (sourceAnswer source))
  | .read (.inr table) next => .read table (fun answer => eraseSources sourceAnswer (next answer))

 theorem eraseSources_value (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (query : FiniteQuery (Sum σ κ)) :
    (eraseSources sourceAnswer query).value tableAnswer =
      query.value (Sum.elim sourceAnswer tableAnswer) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    cases key with
    | inl source => exact ih (sourceAnswer source)
    | inr table => exact ih (tableAnswer table)

 theorem eraseSources_cost (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (tableWeight : κ → ℕ) (query : FiniteQuery (Sum σ κ)) :
    (eraseSources sourceAnswer query).cost tableAnswer tableWeight =
      query.cost (Sum.elim sourceAnswer tableAnswer) (Sum.elim (fun _ => 0) tableWeight) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    cases key with
    | inl source => simpa only [eraseSources, cost, Sum.elim_inl, Nat.zero_add] using ih (sourceAnswer source)
    | inr table => exact congrArg (tableWeight table + ·) (ih (tableAnswer table))

 theorem eraseSources_keys_all (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (query : FiniteQuery (Sum σ κ)) (predicate : κ → Prop)
    (hquery : ∀ key ∈ query.keys (Sum.elim sourceAnswer tableAnswer),
      match key with | .inl _ => True | .inr table => predicate table) :
    ∀ key ∈ (eraseSources sourceAnswer query).keys tableAnswer, predicate key := by
  induction query with
  | done value => intro key hk; exact False.elim (List.not_mem_nil hk)
  | read key next ih =>
    cases key with
    | inl source =>
      apply ih (sourceAnswer source)
      intro key hk
      exact hquery key (List.mem_cons_of_mem _ hk)
    | inr table =>
      intro key hk
      rcases List.mem_cons.mp hk with heq | hk
      · subst key
        exact hquery (.inr table) (List.mem_cons_self ..)
      · apply ih (tableAnswer table) _ key hk
        intro key hk
        exact hquery key (List.mem_cons_of_mem _ hk)

 theorem cost_add_weights {ι : Type*} (answer : ι → ℚ) (left right : ι → ℕ)
    (query : FiniteQuery ι) :
    query.cost answer (fun key => left key + right key) =
      query.cost answer left + query.cost answer right := by
  induction query with
  | done value => rfl
  | read key next ih => simp only [cost, ih]; omega

 theorem cost_mul_weight {ι : Type*} (answer : ι → ℚ) (weight : ι → ℕ)
    (multiplier : ℕ) (query : FiniteQuery ι) :
    query.cost answer (fun key => multiplier * weight key) =
      multiplier * query.cost answer weight := by
  induction query with
  | done value => simp only [cost, Nat.mul_zero]
  | read key next ih => simp only [cost, ih, Nat.mul_add]

 theorem cost_source_table (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (sourceWeight : σ → ℕ) (tableWeight : κ → ℕ) (query : FiniteQuery (Sum σ κ)) :
    query.cost (Sum.elim sourceAnswer tableAnswer) (Sum.elim sourceWeight tableWeight) =
      query.cost (Sum.elim sourceAnswer tableAnswer) (Sum.elim sourceWeight (fun _ => 0)) +
      (eraseSources sourceAnswer query).cost tableAnswer tableWeight := by
  rw [eraseSources_cost, ← cost_add_weights]
  congr 1
  funext key
  cases key <;> simp

end EditApproximation.FiniteQuery

end OAI
