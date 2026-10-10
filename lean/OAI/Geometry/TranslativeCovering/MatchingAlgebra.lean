import OAI.Geometry.TranslativeCovering.CellMatching

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators

universe u_1 u_2

namespace MatchingAlgebra
variable {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]

lemma prod_edges (M : Finset (I × J)) (f : I → J → ℝ) :
    (∏ i, ∏ j, if (i,j) ∈ M then f i j else 1) =
      ∏ e ∈ M, f e.1 e.2 := by
  rw [← Fintype.prod_prod_type (fun e : I × J => if e ∈ M then f e.1 e.2 else 1)]
  rw [← Finset.prod_filter]
  congr 1
  ext e
  simp

noncomputable def leftWeight (M : Finset (I × J)) (a : I → ℝ) (w : I → J → ℝ) (i : I) : ℝ :=
  if h : ∃ j, (i,j) ∈ M then w i h.choose else a i

omit [Fintype I] in
lemma leftWeight_factor (M : Finset (I × J))
    (hm : ∀ i j k, (i,j) ∈ M → (i,k) ∈ M → j = k)
    (a : I → ℝ) (w : I → J → ℝ) (ha : ∀ i, a i ≠ 0) (i : I) :
    leftWeight M a w i = a i * ∏ j, if (i,j) ∈ M then w i j / a i else 1 := by
  by_cases h : ∃ j, (i,j) ∈ M
  · rw [leftWeight, dite_eq_left h]
    have hp : (∏ j, if (i,j) ∈ M then w i j / a i else 1) = w i h.choose / a i := by
      rw [Finset.prod_eq_single h.choose]
      · exact ite_eq_left h.choose_spec
      · intro j _ hj
        apply ite_eq_right
        intro hij
        exact hj (hm i j h.choose hij h.choose_spec)
      · simp
    rw [hp, mul_div_cancel₀ _ (ha i)]
  · rw [leftWeight, dite_eq_right h]
    simp only [not_exists] at h
    simp only [h, ↓reduceIte, Finset.prod_const_one, mul_one]

lemma prod_leftWeight (M : Finset (I × J))
    (hm : ∀ i j k, (i,j) ∈ M → (i,k) ∈ M → j = k)
    (a : I → ℝ) (w : I → J → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∏ i, leftWeight M a w i) = (∏ i, a i) * ∏ e ∈ M, w e.1 e.2 / a e.1 := by
  simp_rw [leftWeight_factor M hm a w ha]
  rw [Finset.prod_mul_distrib, prod_edges]

lemma prod_unmatched_right (M : Finset (I × J))
    (hm : ∀ i j k, (i,k) ∈ M → (j,k) ∈ M → i = j) (b : J → ℝ) :
    (∏ j, b j) = (∏ j : {j : J // ∀ i, (i,j) ∉ M}, b j.val) *
      ∏ e ∈ M, b e.2 := by
  have hproj : Set.InjOn Prod.snd (M : Set (I × J)) := by
    intro e he f hf h
    apply Prod.ext _ h
    exact hm e.1 f.1 e.2 he (by simpa only [h, Prod.mk.eta, Finset.mem_coe] using hf)
  have hsub : (∏ j : {j : J // ∀ i, (i,j) ∉ M}, b j.val) =
      ∏ j ∈ Finset.univ \ M.image Prod.snd, b j := by
    symm
    apply Finset.prod_subtype
    intro j
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h i him
      exact h ⟨(i,j),him,rfl⟩
    · rintro h ⟨⟨i,k⟩,he,rfl⟩
      exact h i he
  rw [hsub, ← Finset.prod_image hproj]
  exact (Finset.prod_sdiff (Finset.subset_univ _)).symm

lemma normalized_diagram_identity (M : Finset (I × J))
    (hl : ∀ i j k, (i,j) ∈ M → (i,k) ∈ M → j = k)
    (hr : ∀ i j k, (i,k) ∈ M → (j,k) ∈ M → i = j)
    (a : I → ℝ) (b : J → ℝ) (w : I → J → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    (∏ i, leftWeight M a w i) * (∏ j : {j : J // ∀ i, (i,j) ∉ M}, b j.val) =
      (∏ i, a i) * (∏ j, b j) * ∏ e ∈ M, w e.1 e.2 / (a e.1 * b e.2) := by
  rw [prod_leftWeight M hl a w ha, prod_unmatched_right M hr b]
  simp_rw [div_mul_eq_div_div, Finset.prod_div_distrib]
  have hp : (∏ e ∈ M, b e.2) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun e _ => hb e.2)
  field_simp
end MatchingAlgebra

end OAI
