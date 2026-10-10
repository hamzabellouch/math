import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteConnectivity

theorem of_poincare
    {α : Type*} [Fintype α] (r : α → α → Prop) (K : α → α → ℝ)
    (γ : ℝ) (hγ : 0 < γ)
    (hrow : ∀ z, ∑ w, K z w = 1)
    (hsupport : ∀ z w, K z w ≠ 0 → z = w ∨ r z w)
    (hgap : ∀ f : α → ℝ,
      γ * ((∑ z, (f z - (∑ w, f w) / (Fintype.card α : ℝ)) ^ 2) /
        (Fintype.card α : ℝ)) ≤
      (∑ z, f z * (f z - ∑ w, K z w * f w)) / (Fintype.card α : ℝ))
    (x y : α) : Relation.ReflTransGen r x y := by
  classical
  by_contra hxy
  let f : α → ℝ := fun z => if Relation.ReflTransGen r x z then 1 else 0
  have hfx : f x = 1 := by simp [f, Relation.ReflTransGen.refl]
  have hfy : f y = 0 := by simp [f, hxy]
  have hclosed (z w : α) (hz : Relation.ReflTransGen r x z)
      (hzw : K z w ≠ 0) : Relation.ReflTransGen r x w := by
    rcases hsupport z w hzw with h | h
    · simpa [← h] using hz
    · exact hz.tail h
  have happly (z : α) (hz : Relation.ReflTransGen r x z) :
      (∑ w, K z w * f w) = 1 := by
    calc
      (∑ w, K z w * f w) = ∑ w, K z w := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hzw : K z w = 0
        · simp [hzw]
        · simp [f, hclosed z w hz hzw]
      _ = 1 := hrow z
  have henergy : (∑ z, f z * (f z - ∑ w, K z w * f w)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : Relation.ReflTransGen r x z
    · rw [happly z hz]
      simp [f, hz]
    · simp [f, hz]
  have hcard : (0 : ℝ) < Fintype.card α := by
    have : Nonempty α := ⟨x⟩
    exact_mod_cast Fintype.card_pos
  have hsum_nonneg : 0 ≤ ∑ z, (f z - (∑ w, f w) / (Fintype.card α : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun z _ => sq_nonneg _
  have hvar_nonpos :
      (∑ z, (f z - (∑ w, f w) / (Fintype.card α : ℝ)) ^ 2) /
        (Fintype.card α : ℝ) ≤ 0 := by
    have hg := hgap f
    rw [henergy, zero_div] at hg
    exact nonpos_of_mul_nonpos_right hg hγ
  have hsum_zero : (∑ z, (f z - (∑ w, f w) / (Fintype.card α : ℝ)) ^ 2) = 0 := by
    apply le_antisymm _ hsum_nonneg
    have h := (div_le_iff₀ hcard).mp hvar_nonpos
    simpa using h
  have hterm (z : α) : (f z - (∑ w, f w) / (Fintype.card α : ℝ)) ^ 2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg _)).mp hsum_zero z
      (Finset.mem_univ z)
  have hx := hterm x
  have hy := hterm y
  rw [hfx] at hx
  rw [hfy] at hy
  nlinarith

end Problem315.FiniteConnectivity

end

end OAI
