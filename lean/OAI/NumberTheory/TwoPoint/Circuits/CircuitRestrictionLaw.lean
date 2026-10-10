import OAI.NumberTheory.TwoPoint.Circuits.CircuitPartialAssignment
import OAI.NumberTheory.TwoPoint.Circuits.CircuitBernoulli

namespace OAI

/-! The three-valued product law for independent random restrictions.
Fixing `s` previously free coordinates changes weight by an exact factor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def restrictionBitLaw (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (Option Bool) where
  weight b := match b with | none => p | some _ => (1 - p) / 2
  nonneg b := by cases b <;> dsimp <;> positivity
  total := by simp [Fintype.sum_option]; ring

noncomputable def restrictionLaw (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (PartialAssignment n) :=
  FiniteLaw.independent (fun _ : Fin n => restrictionBitLaw p hp hp1)

theorem restrictionLaw_assign_weight {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (ρ : PartialAssignment n) (S : Finset (Fin n)) (hS : S ⊆ ρ.free)
    (x : BooleanCube n) :
    (restrictionLaw n p hp hp1.le).weight ρ =
      (2 * p / (1 - p)) ^ S.card *
        (restrictionLaw n p hp hp1.le).weight (ρ.assign S x) := by
  have hn : 1 - p ≠ 0 := by linarith
  have hpoint (i : Fin n) :
      (restrictionBitLaw p hp hp1.le).weight (ρ i) =
        (if i ∈ S then 2 * p / (1 - p) else 1) *
          (restrictionBitLaw p hp hp1.le).weight (ρ.assign S x i) := by
    by_cases hi : i ∈ S
    · have hρ := (mem_filter.mp (hS hi)).2
      simp only [restrictionBitLaw, PartialAssignment.assign, hi, hρ, ite_true]
      field_simp
    · simp [PartialAssignment.assign, hi]
  change (∏ i, (restrictionBitLaw p hp hp1.le).weight (ρ i)) = _
  simp_rw [hpoint]
  rw [prod_mul_distrib, Fintype.prod_ite_mem, prod_const]
  rfl

theorem FiniteLaw.probability_le_of_encoding {α β : Type*}
    [Fintype α] [Fintype β] (μ : FiniteLaw α) (E : α → Prop)
    (encode : α → α × β) (r : ℝ) (hr : 0 ≤ r)
    (hinj : ∀ x, E x → ∀ y, E y → encode x = encode y → x = y)
    (hweight : ∀ x, E x → μ.weight x ≤ r * μ.weight (encode x).1) :
    μ.probability E ≤ Fintype.card β * r := by
  calc
    μ.probability E = ∑ x ∈ (univ : Finset α).filter E, μ.weight x := by
      simp [FiniteLaw.probability, FiniteLaw.average, sum_filter, mul_ite]
    _ ≤ ∑ y : α × β, r * μ.weight y.1 := by
      apply sum_le_sum_of_injOn encode
      · intro x hx y hy h
        exact hinj x (mem_filter.mp hx).2 y (mem_filter.mp hy).2 h
      · exact fun _ _ => mem_univ _
      · exact fun x hx => hweight x (mem_filter.mp hx).2
      · exact fun y _ _ => mul_nonneg hr (μ.nonneg y.1)
    _ = Fintype.card β * r := by
      simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul]
      rw [← mul_sum, ← mul_sum, μ.total]
      ring

end TwoPointCorrelations

end OAI
