import OAI.NumberTheory.EgyptianFractions.HitCount

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

/-- The finite-set word model agrees exactly with independent samples in the alphabet subtype. -/
theorem typed_sample_event_card {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (R : (Fin t → α) → Prop) [DecidablePred R] :
    Fintype.card {f : Fin t → P // R (fun i => (f i : α))} =
      ((sampleWords P t).filter R).card := by
  classical
  let E : {f : Fin t → P // R (fun i => (f i : α))} ≃
      {f : Fin t → α // f ∈ (sampleWords P t).filter R} := {
    toFun := fun f => ⟨fun i => (f.1 i : α), Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr (fun i => (f.1 i).property), f.2⟩⟩
    invFun := fun f => ⟨fun i => ⟨f.1 i,
      Fintype.mem_piFinset.mp (Finset.mem_filter.mp f.2).1 i⟩,
      (Finset.mem_filter.mp f.2).2⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext i
      apply Subtype.ext
      rfl
    right_inv := by
      intro f
      apply Subtype.ext
      rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr E

/-- Reindexing a finite sample index type preserves all product-dependent event counts. -/
theorem typed_product_event_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (R : ℕ → Prop) [DecidablePred R] :
    Fintype.card {f : ι → P // R (∏ i, (f i : ℕ))} =
      ((sampleWords P (Fintype.card ι)).filter (fun f => R (∏ i, f i))).card := by
  classical
  let e := Fintype.equivFin ι
  let E : (ι → P) ≃ (Fin (Fintype.card ι) → P) := Equiv.piCongrLeft' (fun _ => P) e
  have hprod : ∀ f : ι → P, (∏ j, ((E f) j : ℕ)) = ∏ i, (f i : ℕ) := by
    intro f
    change (∏ j, (f (e.symm j) : ℕ)) = ∏ i, (f i : ℕ)
    exact e.symm.prod_comp (fun i => (f i : ℕ))
  have hcard : Fintype.card {f : ι → P // R (∏ i, (f i : ℕ))} =
      Fintype.card {f : Fin (Fintype.card ι) → P // R (∏ i, (f i : ℕ))} := by
    apply Fintype.card_congr
    exact E.subtypeEquiv (fun f => by rw [hprod])
  exact hcard.trans (typed_sample_event_card P (Fintype.card ι) (fun f => R (∏ i, f i)))

/-- Normalized version, suitable for an exposed block of independent typed samples. -/
theorem typed_product_event_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (R : ℕ → Prop) [DecidablePred R] :
    (Fintype.card {f : ι → P // R (∏ i, (f i : ℕ))} : ℝ) /
        (Fintype.card (ι → P) : ℝ) =
      (((sampleWords P (Fintype.card ι)).filter (fun f => R (∏ i, f i))).card : ℝ) /
        (P.card : ℝ) ^ (Fintype.card ι) := by
  rw [typed_product_event_card]
  simp only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow]

/-- Independent uniform sampling has uniform marginals on every subset of coordinates. -/
theorem restriction_event_probability {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β] (s : Finset ι) (R : (s → β) → Prop) [DecidablePred R] :
    (Fintype.card {f : ι → β // R (fun i : s => f i)} : ℝ) /
        (Fintype.card (ι → β) : ℝ) =
      (Fintype.card {g : s → β // R g} : ℝ) / (Fintype.card (s → β) : ℝ) := by
  classical
  let E := Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ => β)
  have hcard : Fintype.card {f : ι → β // R (fun i : s => f i)} =
      Fintype.card {g : s → β // R g} * Fintype.card ({i : ι // i ∉ s} → β) := by
    rw [← Fintype.card_prod]
    apply Fintype.card_congr
    exact (E.subtypeEquiv (fun f => Iff.rfl)).trans Equiv.prodSubtypeFstEquivSubtypeProd
  have htotal : Fintype.card (ι → β) =
      Fintype.card (s → β) * Fintype.card ({i : ι // i ∉ s} → β) := by
    simpa only [Fintype.card_prod] using Fintype.card_congr E
  rw [hcard, htotal]
  push_cast
  have hrest : (Fintype.card ({i : ι // i ∉ s} → β) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ({i : ι // i ∉ s} → β) ≠ 0)
  exact mul_div_mul_right _ _ hrest

/-- A product over a subset of labelled coordinates has the ordinary independent-product law. -/
theorem restricted_product_event_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) [Nonempty P] (s : Finset ι) (R : ℕ → Prop) [DecidablePred R] :
    (Fintype.card {f : ι → P // R (∏ i : s, (f i : ℕ))} : ℝ) /
        (Fintype.card (ι → P) : ℝ) =
      (((sampleWords P (Fintype.card s)).filter (fun f => R (∏ i, f i))).card : ℝ) /
        (P.card : ℝ) ^ (Fintype.card s) := by
  rw [restriction_event_probability s (fun g : s → P => R (∏ i, (g i : ℕ)))]
  exact typed_product_event_probability (ι := s) P R

end Problem337.RandomProducts

end OAI
