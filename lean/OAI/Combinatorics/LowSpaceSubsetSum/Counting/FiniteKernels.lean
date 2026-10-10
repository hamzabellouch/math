import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SurvivalLayout

namespace OAI

/-!
# Finite dependent sampling kernels

A dependent second draw uses its own normalized mass in each first-draw
fiber. In particular, this construction does not replace sequential uniform
draws with the generally different uniform law on their sigma type.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

universe u v

structure FiniteLaw (Ω : Type u) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

namespace FiniteLaw

variable {Ω : Type u} [Fintype Ω]

noncomputable def probability (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.mass ω else 0

theorem probability_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.probability P := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  by_cases h : P ω
  · simpa only [h, ↓reduceIte] using μ.nonneg ω
  · simp only [h, ↓reduceIte, le_refl]

theorem probability_true (μ : FiniteLaw Ω) : μ.probability (fun _ => True) = 1 := by
  classical
  simpa only [probability, ↓reduceIte] using μ.total

theorem probability_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop}
    (h : ∀ ω, P ω → Q ω) : μ.probability P ≤ μ.probability Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp only [hp, h ω hp, ↓reduceIte, le_refl]
  · simp only [hp, ↓reduceIte]
    by_cases hq : Q ω
    · simpa only [hq, ↓reduceIte] using μ.nonneg ω
    · simp only [hq, ↓reduceIte, le_refl]

theorem probability_le_one (μ : FiniteLaw Ω) (P : Ω → Prop) : μ.probability P ≤ 1 := by
  rw [← μ.probability_true]
  exact μ.probability_mono (fun _ _ => trivial)

theorem probability_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.probability (fun ω => ¬P ω) = 1 - μ.probability P := by
  classical
  have h : μ.probability (fun ω => ¬P ω) + μ.probability P = 1 := by
    rw [probability, probability, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  linarith

noncomputable def uniform [Nonempty Ω] : FiniteLaw Ω where
  mass _ := 1 / Fintype.card Ω
  nonneg _ := by positivity
  total := by
    have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [h]

theorem uniform_probability [Nonempty Ω] (P : Ω → Prop) :
    (uniform : FiniteLaw Ω).probability P = finiteUniformProbability P := by
  classical
  rw [finiteUniformProbability_eq_indicator_mean, probability, Finset.sum_div]
  simp only [uniform, ite_div, one_div, zero_div]

/-- The output retains the preceding draw, making its dependence explicit. -/
noncomputable def bind (μ : FiniteLaw Ω) (Ψ : Ω → Type v)
    [∀ ω, Fintype (Ψ ω)] (K : ∀ ω, FiniteLaw (Ψ ω)) : FiniteLaw (Σ ω, Ψ ω) where
  mass z := μ.mass z.1 * (K z.1).mass z.2
  nonneg z := mul_nonneg (μ.nonneg _) ((K _).nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (K _).total, mul_one]
    exact μ.total

theorem bind_probability (μ : FiniteLaw Ω) (Ψ : Ω → Type v)
    [∀ ω, Fintype (Ψ ω)] (K : ∀ ω, FiniteLaw (Ψ ω))
    (P : (Σ ω, Ψ ω) → Prop) :
    (μ.bind Ψ K).probability P =
      ∑ ω, μ.mass ω * (K ω).probability (fun y => P ⟨ω, y⟩) := by
  classical
  simp only [probability, bind, Fintype.sum_sigma, Finset.mul_sum, mul_ite, mul_zero]

theorem bind_first_probability (μ : FiniteLaw Ω) (Ψ : Ω → Type v)
    [∀ ω, Fintype (Ψ ω)] (K : ∀ ω, FiniteLaw (Ψ ω)) (P : Ω → Prop) :
    (μ.bind Ψ K).probability (fun z => P z.1) = μ.probability P := by
  classical
  rw [bind_probability, probability]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hp : P ω
  · simp only [probability, hp, ↓reduceIte, (K ω).total, mul_one]
  · simp [probability, hp]

theorem bind_good_lower (μ : FiniteLaw Ω) (Ψ : Ω → Type v)
    [∀ ω, Fintype (Ψ ω)] (K : ∀ ω, FiniteLaw (Ψ ω))
    (P : Ω → Prop) (Q : ∀ ω, Ψ ω → Prop) {p q : ℝ}
    (hq : 0 ≤ q) (hp : p ≤ μ.probability P)
    (hQ : ∀ ω, P ω → q ≤ (K ω).probability (Q ω)) :
    p * q ≤ (μ.bind Ψ K).probability (fun z => P z.1 ∧ Q z.1 z.2) := by
  classical
  apply (mul_le_mul_of_nonneg_right hp hq).trans
  rw [bind_probability, probability, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hP : P ω
  · simpa only [hP, ↓reduceIte, true_and] using
      mul_le_mul_of_nonneg_left (hQ ω hP) (μ.nonneg ω)
  · simp [hP, probability]

theorem probability_inter_ge_sub (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.probability P - μ.probability (fun ω => ¬Q ω) ≤
      μ.probability (fun ω => P ω ∧ Q ω) := by
  classical
  have h : μ.probability P ≤ μ.probability (fun ω => P ω ∧ Q ω) +
      μ.probability (fun ω => ¬Q ω) := by
    rw [probability, probability, probability, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]
  linarith

theorem probability_eq (μ : FiniteLaw Ω) (ω : Ω) :
    μ.probability (fun x => x = ω) = μ.mass ω := by
  classical
  simp [probability]

/-- Conditioning on one retained history leaves exactly its prescribed
next-draw law. The formula is valid even when that history has zero mass. -/
theorem bind_point_probability (μ : FiniteLaw Ω) (Ψ : Ω → Type v)
    [∀ ω, Fintype (Ψ ω)] (K : ∀ ω, FiniteLaw (Ψ ω))
    (Q : ∀ ω, Ψ ω → Prop) (ω : Ω) :
    (μ.bind Ψ K).probability (fun z => z.1 = ω ∧ Q z.1 z.2) =
      μ.mass ω * (K ω).probability (Q ω) := by
  classical
  rw [bind_probability]
  rw [Finset.sum_eq_single ω]
  · simp only [true_and]
  · intro x _ hx
    simp [hx, probability]
  · simp

theorem bind_conditional_probability (μ : FiniteLaw Ω) (Ψ : Ω → Type v)
    [∀ ω, Fintype (Ψ ω)] (K : ∀ ω, FiniteLaw (Ψ ω))
    (Q : ∀ ω, Ψ ω → Prop) (ω : Ω) (hω : μ.mass ω ≠ 0) :
    (μ.bind Ψ K).probability (fun z => z.1 = ω ∧ Q z.1 z.2) /
      μ.probability (fun x => x = ω) = (K ω).probability (Q ω) := by
  rw [bind_point_probability, probability_eq]
  exact mul_div_cancel_left₀ _ hω

end FiniteLaw

end LowSpaceSubsetSum

end OAI
