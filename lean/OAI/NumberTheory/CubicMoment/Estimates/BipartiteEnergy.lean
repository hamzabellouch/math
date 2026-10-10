import OAI.NumberTheory.CubicMoment.Estimates.PairOverlapEnergy

namespace OAI

/-! A two-sided incidence bound with independent coefficient energies. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bipartite_sum_sq_le {α β : Type*} (P : Finset α) (B : Finset β)
    (R : α → β → Prop) [DecidableRel R] (a : α → ℝ) (b : β → ℝ) {M N : ℝ}
    (hM : 0 ≤ M) (_hN : 0 ≤ N)
    (hrow : ∀ x ∈ P, ((B.filter (R x)).card:ℝ) ≤ M)
    (hcol : ∀ y ∈ B, ((P.filter (fun x => R x y)).card:ℝ) ≤ N) :
    (∑ x ∈ P, ∑ y ∈ B, if R x y then a x*b y else 0)^2 ≤
      (M*∑ x ∈ P, (a x)^2)*(N*∑ y ∈ B, (b y)^2) := by
  let E := (P ×ˢ B).filter (fun p => R p.1 p.2)
  have hs : (∑ p ∈ E, a p.1*b p.2) =
      ∑ x ∈ P, ∑ y ∈ B, if R x y then a x*b y else 0 := by
    rw [Finset.sum_filter,Finset.sum_product]
  have hx : (∑ p ∈ E, (a p.1)^2) ≤ M*∑ x ∈ P, (a x)^2 := by
    rw [Finset.sum_filter,Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hrow x hx) (sq_nonneg _)
  have hy : (∑ p ∈ E, (b p.2)^2) ≤ N*∑ y ∈ B, (b y)^2 := by
    rw [Finset.sum_filter,Finset.sum_product,Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcol y hy) (sq_nonneg _)
  rw [←hs]
  exact (Finset.sum_mul_sq_le_sq_mul_sq E _ _).trans
    (mul_le_mul hx hy (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg hM (Finset.sum_nonneg fun _ _ => sq_nonneg _)))

lemma noncoprime_bipartite_energy (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) {Y D : ℝ} (hY : 0 ≤ Y) (hD : 0 < D)
    (hP : ∀ a ∈ P, a ≠ 0 ∧ norm a ≤ Y)
    (hB : ∀ b ∈ B, primary b ∧ Squarefree b) (n : ℕ)
    (hn : ∀ b ∈ B, (primaryPrimeFactors b).card ≤ n)
    (hrough : ∀ b ∈ B, ∀ p ∈ primaryPrimeFactors b, D ≤ norm p) :
    (∑ a ∈ P, ∑ b ∈ B, if ¬IsCoprime a b then ‖α a‖*‖β b‖ else 0)^2 ≤
      ((B.card:ℝ)*∑ a ∈ P, ‖α a‖^2)*
        ((n:ℝ)*(18*Y/D)*∑ b ∈ B, ‖β b‖^2) := by
  have hrow (a : Eisenstein) (_ha : a ∈ P) :
      ((B.filter (fun b => ¬IsCoprime a b)).card:ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_filter_le B (fun b => ¬IsCoprime a b)
  have hcol (b : Eisenstein) (hb : b ∈ B) :
      ((P.filter (fun a => ¬IsCoprime a b)).card:ℝ) ≤ (n:ℝ)*(18*Y/D) := by
    have he : P.filter (fun a => ¬IsCoprime a b) = P.filter (fun a => ¬IsCoprime b a) := by
      ext a
      simp only [Finset.mem_filter,isCoprime_comm]
    rw [he]
    exact (noncoprime_row_card_le P hY hD hP (hB b hb).1 (hB b hb).2 (hrough b hb)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hn b hb) (by positivity))
  simpa only [ite_not] using bipartite_sum_sq_le P B (fun a b => ¬IsCoprime a b)
    (fun a => ‖α a‖) (fun b => ‖β b‖) (M := (B.card:ℝ))
    (N := (n:ℝ)*(18*Y/D)) (Nat.cast_nonneg _) (by positivity) hrow hcol

end CubicFirstMoment

end

end OAI
