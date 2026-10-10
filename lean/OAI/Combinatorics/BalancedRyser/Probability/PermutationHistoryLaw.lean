import OAI.Combinatorics.BalancedRyser.Probability.PermutationSubsetLaw

namespace OAI

open scoped BigOperators

namespace Balanced.PermutationHistoryLaw

noncomputable section
open Finset PermutationSubsetLaw

variable {α : Type*} [Fintype α] [DecidableEq α]

def histories (I : Finset α) (σ₀ : Equiv.Perm α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun σ => ∀ j ∈ I, σ j = σ₀ j

@[simp] theorem mem_histories (I : Finset α) (σ₀ σ : Equiv.Perm α) :
    σ ∈ histories I σ₀ ↔ ∀ j ∈ I, σ j = σ₀ j := by
  simp [histories]

theorem histories_nonempty (I : Finset α) (σ₀ : Equiv.Perm α) :
    (histories I σ₀).Nonempty := by
  exact ⟨σ₀, by simp⟩

def unused (I : Finset α) (σ₀ : Equiv.Perm α) : Finset α :=
  Finset.univ \ I.map σ₀.toEmbedding

theorem next_mem_unused (I : Finset α) (σ₀ : Equiv.Perm α)
    (i : α) (hi : i ∉ I) (σ : Equiv.Perm α) (hσ : σ ∈ histories I σ₀) :
    σ i ∈ unused I σ₀ := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro h
  obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp h
  have hval := (mem_histories I σ₀ σ).mp hσ j hj
  have hji : j = i := σ.injective (hval.trans heq)
  exact hi (hji ▸ hj)

theorem unused_nonempty (I : Finset α) (σ₀ : Equiv.Perm α)
    (i : α) (hi : i ∉ I) : (unused I σ₀).Nonempty :=
  ⟨σ₀ i, next_mem_unused I σ₀ i hi σ₀ (by simp)⟩

@[simp] theorem card_unused (I : Finset α) (σ₀ : Equiv.Perm α) :
    (unused I σ₀).card = Fintype.card α - I.card := by
  simp [unused, Finset.card_sdiff_of_subset (Finset.subset_univ _)]

theorem swap_preserves_history (I : Finset α) (σ₀ σ : Equiv.Perm α)
    (x y : α) (hx : x ∈ unused I σ₀) (hy : y ∈ unused I σ₀)
    (hσ : σ ∈ histories I σ₀) :
    σ.trans (Equiv.swap x y) ∈ histories I σ₀ := by
  apply (mem_histories _ _ _).mpr
  intro j hj
  have hval := (mem_histories I σ₀ σ).mp hσ j hj
  change Equiv.swap x y (σ j) = σ₀ j
  rw [hval]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact (Finset.mem_sdiff.mp hx).2
      (Finset.mem_map.mpr ⟨j, hj, h⟩)
  · intro h
    exact (Finset.mem_sdiff.mp hy).2
      (Finset.mem_map.mpr ⟨j, hj, h⟩)

theorem next_fiber_card_eq (I : Finset α) (σ₀ : Equiv.Perm α) (i x y : α)
    (hx : x ∈ unused I σ₀) (hy : y ∈ unused I σ₀) :
    ((histories I σ₀).filter (fun σ => σ i = x)).card =
      ((histories I σ₀).filter (fun σ => σ i = y)).card := by
  apply Finset.card_equiv (postcompose (Equiv.swap x y))
  intro σ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hσ, hi⟩
    refine ⟨swap_preserves_history I σ₀ σ x y hx hy hσ, ?_⟩
    change Equiv.swap x y (σ i) = y
    simp [hi]
  · rintro ⟨hσ, hi⟩
    have hback := swap_preserves_history I σ₀
      (σ.trans (Equiv.swap x y)) x y hx hy hσ
    have hσ' : σ ∈ histories I σ₀ := by
      simpa using hback
    refine ⟨hσ', ?_⟩
    change Equiv.swap x y (σ i) = y at hi
    apply (Equiv.swap x y).injective
    simpa using hi

theorem expect_next (I : Finset α) (σ₀ : Equiv.Perm α)
    (i : α) (hi : i ∉ I) (g : α → ℝ) :
    (𝔼 σ ∈ histories I σ₀, g (σ i)) = 𝔼 x ∈ unused I σ₀, g x := by
  let m := ((histories I σ₀).filter (fun σ => σ i = σ₀ i)).card
  have hm : 0 < m := by
    apply Finset.card_pos.mpr
    exact ⟨σ₀, by simp⟩
  apply expect_comp_of_fiber_card_eq (histories I σ₀) (unused I σ₀)
    (fun σ => σ i) m hm (fun σ hσ => next_mem_unused I σ₀ i hi σ hσ)
  intro x hx
  exact next_fiber_card_eq I σ₀ i x (σ₀ i) hx
    (next_mem_unused I σ₀ i hi σ₀ (by simp))

theorem next_probability (I : Finset α) (σ₀ : Equiv.Perm α)
    (i : α) (hi : i ∉ I) (x : α) :
    (𝔼 σ ∈ histories I σ₀, if σ i = x then (1 : ℝ) else 0) =
      if x ∈ unused I σ₀ then ((Fintype.card α - I.card : ℕ) : ℝ)⁻¹ else 0 := by
  rw [expect_next I σ₀ i hi (fun y => if y = x then (1 : ℝ) else 0)]
  rw [Finset.expect_eq_sum_div_card]
  by_cases hx : x ∈ unused I σ₀ <;> simp [hx, card_unused]

theorem histories_card_eq (I : Finset α) (σ₀ τ₀ : Equiv.Perm α) :
    (histories I σ₀).card = (histories I τ₀).card := by
  apply Finset.card_equiv (postcompose (σ₀.symm.trans τ₀))
  intro σ
  simp only [mem_histories]
  constructor
  · intro h j hj
    change τ₀ (σ₀.symm (σ j)) = τ₀ j
    simp [h j hj]
  · intro h j hj
    have heq : τ₀ (σ₀.symm (σ j)) = τ₀ j := h j hj
    exact (Equiv.symm_apply_eq σ₀).mp (τ₀.injective heq)

theorem histories_symm (I : Finset α) (σ τ : Equiv.Perm α) :
    σ ∈ histories I τ ↔ τ ∈ histories I σ := by
  simp only [mem_histories]
  exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩

theorem expect_histories (I : Finset α) (g : Equiv.Perm α → ℝ) :
    (𝔼 τ : Equiv.Perm α, 𝔼 σ ∈ histories I τ, g σ) =
      𝔼 σ : Equiv.Perm α, g σ := by
  let m := (histories I (Equiv.refl α)).card
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast (histories_nonempty I (Equiv.refl α)).card_pos.ne'
  have hc (τ : Equiv.Perm α) : (histories I τ).card = m :=
    histories_card_eq I τ (Equiv.refl α)
  simp only [Finset.expect_eq_sum_div_card, hc]
  rw [← Finset.sum_div]
  have hs : (∑ τ : Equiv.Perm α, ∑ σ ∈ histories I τ, g σ) =
      (m : ℝ) * ∑ σ : Equiv.Perm α, g σ := by
    calc
      _ = ∑ τ : Equiv.Perm α, ∑ σ : Equiv.Perm α,
          if σ ∈ histories I τ then g σ else 0 := by
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ σ : Equiv.Perm α, ∑ τ : Equiv.Perm α,
          if σ ∈ histories I τ then g σ else 0 := Finset.sum_comm
      _ = ∑ σ : Equiv.Perm α, (m : ℝ) * g σ := by
        apply Finset.sum_congr rfl
        intro σ _
        simp_rw [histories_symm I σ]
        simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          nsmul_eq_mul, hc]
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hs]
  field_simp

theorem expect_past_next (I : Finset α) (i : α) (hi : i ∉ I)
    (f : Equiv.Perm α → α → ℝ)
    (hf : ∀ σ τ, σ ∈ histories I τ → f σ = f τ) :
    (𝔼 σ : Equiv.Perm α, f σ (σ i)) =
      𝔼 τ : Equiv.Perm α, 𝔼 x ∈ unused I τ, f τ x := by
  rw [← expect_histories I (fun σ => f σ (σ i))]
  apply Finset.expect_congr rfl
  intro τ _
  calc
    (𝔼 σ ∈ histories I τ, f σ (σ i)) =
        𝔼 σ ∈ histories I τ, f τ (σ i) := by
      apply Finset.expect_congr rfl
      intro σ hσ
      rw [hf σ τ hσ]
    _ = _ := expect_next I τ i hi (f τ)

theorem map_eq_of_history (I : Finset α) (σ τ : Equiv.Perm α)
    (h : σ ∈ histories I τ) : I.map σ.toEmbedding = I.map τ.toEmbedding := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, heq⟩
    refine ⟨j, hj, ?_⟩
    exact ((mem_histories I τ σ).mp h j hj).symm.trans heq
  · rintro ⟨j, hj, heq⟩
    refine ⟨j, hj, ?_⟩
    exact ((mem_histories I τ σ).mp h j hj).trans heq

theorem expect_by_image (I : Finset α) (g : Equiv.Perm α → ℝ) :
    (𝔼 σ : Equiv.Perm α, g σ) =
      𝔼 S ∈ (Finset.univ : Finset α).powersetCard I.card,
        𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α =>
          I.map σ.toEmbedding = S), g σ := by
  apply expect_eq_expect_fiber_of_card_eq (Finset.univ : Finset (Equiv.Perm α))
    ((Finset.univ : Finset α).powersetCard I.card)
    (fun σ : Equiv.Perm α => I.map σ.toEmbedding)
    ((Finset.univ.filter (fun σ : Equiv.Perm α => I.map σ.toEmbedding = I)).card)
  · intro σ _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩
  · intro S hS
    exact image_fiber_card_eq I S I (Finset.mem_powersetCard.mp hS).2

omit [DecidableEq α] in

theorem uniform_measureReal_eq_expect [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (A : α → Prop) [DecidablePred A] :
    (PMF.uniformOfFintype α).toMeasure.real {ω | A ω} =
      𝔼 ω : α, if A ω then (1 : ℝ) else 0 := by
  classical
  unfold MeasureTheory.Measure.real
  rw [PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    Fintype.card_subtype, Finset.expect_eq_sum_div_card,
    Finset.sum_boole, Finset.card_univ, Set.mem_ofPred_eq]

end
end Balanced.PermutationHistoryLaw

end OAI
