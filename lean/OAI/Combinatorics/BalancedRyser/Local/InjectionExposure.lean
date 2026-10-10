import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform

namespace OAI

namespace Balanced.InjectionExposure

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def completions (K : Finset I) (base : I ↪ J) : Finset (I ↪ J) :=
  Finset.univ.filter (fun e => ∀ j ∈ K, e j = base j)

def remaining (K : Finset I) (base : I ↪ J) : Finset J :=
  Finset.univ \ K.image base

@[simp] theorem mem_completions (K : Finset I) (base e : I ↪ J) :
    e ∈ completions K base ↔ ∀ j ∈ K, e j = base j := by
  simp [completions]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem mem_remaining (K : Finset I) (base : I ↪ J) (a : J) :
    a ∈ remaining K base ↔ a ∉ K.image base := by
  simp [remaining]

theorem completions_nonempty (K : Finset I) (base : I ↪ J) :
    (completions K base).Nonempty := by
  exact ⟨base, by simp⟩

theorem value_mem_remaining (K : Finset I) (base e : I ↪ J)
    (he : e ∈ completions K base) (i : I) (hi : i ∉ K) :
    e i ∈ remaining K base := by
  rw [mem_remaining]
  intro h
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
  have hsame : e j = e i := (mem_completions K base e).mp he j hj |>.trans hji
  exact hi (e.injective hsame ▸ hj)

theorem base_mem_remaining (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) : base i ∈ remaining K base :=
  value_mem_remaining K base base (by simp) i hi

omit [Fintype I] [DecidableEq I] in
theorem card_remaining (K : Finset I) (base : I ↪ J) :
    (remaining K base).card = Fintype.card J - K.card := by
  rw [remaining, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Finset.card_image_of_injective _ base.injective]

theorem swap_mem_completions (K : Finset I) (base e : I ↪ J)
    (he : e ∈ completions K base) (a b : J)
    (ha : a ∈ remaining K base) (hb : b ∈ remaining K base) :
    e.trans (Equiv.swap a b).toEmbedding ∈ completions K base := by
  rw [mem_completions] at he ⊢
  intro j hj
  change Equiv.swap a b (e j) = base j
  rw [he j hj]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact (mem_remaining K base a).mp ha (Finset.mem_image.mpr ⟨j, hj, h⟩)
  · intro h
    exact (mem_remaining K base b).mp hb (Finset.mem_image.mpr ⟨j, hj, h⟩)

theorem fibre_card_eq (K : Finset I) (base : I ↪ J) (i : I)
    (a b : J) (ha : a ∈ remaining K base) (hb : b ∈ remaining K base) :
    ((completions K base).filter (fun e => e i = a)).card =
      ((completions K base).filter (fun e => e i = b)).card := by
  let swapOutput : (I ↪ J) → (I ↪ J) :=
    fun e => e.trans (Equiv.swap a b).toEmbedding
  have hinv (e : I ↪ J) : swapOutput (swapOutput e) = e := by
    ext j
    exact Equiv.swap_apply_self a b (e j)
  have hmap (e : I ↪ J)
      (he : e ∈ (completions K base).filter (fun e => e i = a)) :
      swapOutput e ∈ (completions K base).filter (fun e => e i = b) := by
    obtain ⟨he, hei⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨swap_mem_completions K base e he a b ha hb, ?_⟩
    change Equiv.swap a b (e i) = b
    rw [hei, Equiv.swap_apply_left]
  have hmap' (e : I ↪ J)
      (he : e ∈ (completions K base).filter (fun e => e i = b)) :
      swapOutput e ∈ (completions K base).filter (fun e => e i = a) := by
    obtain ⟨he, hei⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨swap_mem_completions K base e he a b ha hb, ?_⟩
    change Equiv.swap a b (e i) = a
    rw [hei, Equiv.swap_apply_right]
  exact Finset.card_bij' (fun e _ => swapOutput e) (fun e _ => swapOutput e)
    hmap hmap' (fun e _ => hinv e) (fun e _ => hinv e)

theorem card_completions_eq (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) (a : J) (ha : a ∈ remaining K base) :
    (completions K base).card = (remaining K base).card *
      ((completions K base).filter (fun e => e i = a)).card := by
  calc
    (completions K base).card =
        ∑ b ∈ remaining K base,
          ((completions K base).filter (fun e => e i = b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun e he =>
        value_mem_remaining K base e he i hi)
    _ = ∑ _b ∈ remaining K base,
          ((completions K base).filter (fun e => e i = a)).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact fibre_card_eq K base i b a hb ha
    _ = _ := by simp

theorem next_value_probability (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) (a : J) (ha : a ∈ remaining K base) :
    ((PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).toOuterMeasure
      {e | e i = a}).toReal = 1 / ((remaining K base).card : ℝ) := by
  classical
  have hC : 0 < ((completions K base).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (completions_nonempty K base)
  have hR : 0 < ((remaining K base).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (show (remaining K base).Nonempty from ⟨a, ha⟩)
  have hfactor : ((completions K base).card : ℝ) =
      ((remaining K base).card : ℝ) *
        (((completions K base).filter (fun e => e i = a)).card : ℝ) := by
    exact_mod_cast card_completions_eq K base i hi a ha
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  apply (div_eq_div_iff (ne_of_gt hC) (ne_of_gt hR)).mpr
  nlinarith

theorem next_value_probability_card (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) (a : J) (ha : a ∈ remaining K base) :
    ((PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).toOuterMeasure
      {e | e i = a}).toReal = 1 / ((Fintype.card J - K.card : ℕ) : ℝ) := by
  rw [next_value_probability K base i hi a ha, card_remaining]

theorem event_card_eq (K : Finset I) (base : I ↪ J) (i : I) (hi : i ∉ K)
    (P : J → Prop) [DecidablePred P] :
    ((completions K base).filter (fun e => P (e i))).card =
      ((remaining K base).filter P).card *
        ((completions K base).filter (fun e => e i = base i)).card := by
  calc
    ((completions K base).filter (fun e => P (e i))).card =
        ∑ b ∈ (remaining K base).filter P,
          (((completions K base).filter (fun e => P (e i))).filter
            (fun e => e i = b)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro e he
      obtain ⟨he, hPe⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨value_mem_remaining K base e he i hi, hPe⟩
    _ = ∑ _b ∈ (remaining K base).filter P,
        ((completions K base).filter (fun e => e i = base i)).card := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨hb, hPb⟩ := Finset.mem_filter.mp hb
      have hfibre : ((completions K base).filter (fun e => P (e i))).filter
          (fun e => e i = b) = (completions K base).filter (fun e => e i = b) := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · intro h
          exact ⟨⟨h.1, h.2 ▸ hPb⟩, h.2⟩
      rw [hfibre]
      exact fibre_card_eq K base i b (base i) hb (base_mem_remaining K base i hi)
    _ = _ := by simp

theorem next_event_probability (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) (P : J → Prop) [DecidablePred P] :
    ((PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).toOuterMeasure
      {e | P (e i)}).toReal =
        (((remaining K base).filter P).card : ℝ) / ((remaining K base).card : ℝ) := by
  classical
  have hC : 0 < ((completions K base).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (completions_nonempty K base)
  have hR : 0 < ((remaining K base).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (show (remaining K base).Nonempty from ⟨base i, base_mem_remaining K base i hi⟩)
  have hfactor : ((completions K base).card : ℝ) =
      ((remaining K base).card : ℝ) *
        (((completions K base).filter (fun e => e i = base i)).card : ℝ) := by
    exact_mod_cast card_completions_eq K base i hi (base i) (base_mem_remaining K base i hi)
  have hevent : (((completions K base).filter (fun e => P (e i))).card : ℝ) =
      (((remaining K base).filter P).card : ℝ) *
        (((completions K base).filter (fun e => e i = base i)).card : ℝ) := by
    exact_mod_cast event_card_eq K base i hi P
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  apply (div_eq_div_iff (ne_of_gt hC) (ne_of_gt hR)).mpr
  rw [hfactor, hevent]
  ring

theorem next_event_probability_le (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) (P : J → Prop) [DecidablePred P]
    (hP : ((remaining K base).filter P).card ≤ 1) :
    ((PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).toOuterMeasure
      {e | P (e i)}).toReal ≤ 1 / ((remaining K base).card : ℝ) := by
  rw [next_event_probability K base i hi P]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hP) (Nat.cast_nonneg _)

theorem next_event_probability_le_budget (K : Finset I) (base : I ↪ J)
    (i : I) (hi : i ∉ K) (P : J → Prop) [DecidablePred P]
    (hP : ((remaining K base).filter P).card ≤ 1)
    (N : ℕ) (hK : K.card ≤ N) (hN : N < Fintype.card J) :
    ((PMF.uniformOfFinset (completions K base) (completions_nonempty K base)).toOuterMeasure
      {e | P (e i)}).toReal ≤ 1 / ((Fintype.card J - N : ℕ) : ℝ) := by
  apply (next_event_probability_le K base i hi P hP).trans
  rw [card_remaining]
  apply one_div_le_one_div_of_le
  · exact_mod_cast Nat.sub_pos_of_lt hN
  · exact_mod_cast Nat.sub_le_sub_left hK (Fintype.card J)

end Balanced.InjectionExposure

end OAI
