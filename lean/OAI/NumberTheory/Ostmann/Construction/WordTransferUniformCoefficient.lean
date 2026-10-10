import OAI.NumberTheory.Ostmann.Construction.WordTransferWeightIdentity

namespace OAI

/-! # The original bounded-bin recursive weight is the constructed coefficient -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem list_prod_complex_gate {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] (F : α → ℂ) :
    (l.map (fun a => (if P a then (1 : ℂ) else 0) * F a)).prod =
      (if ∀ a ∈ l, P a then 1 else 0) * (l.map F).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.mem_cons, forall_eq_or_imp]
    split_ifs <;> simp_all

theorem list_prod_getElem_of_length {α : Type*} (l : List α) (m : ℕ) (hl : l.length = m)
    (F : α → ℂ) :
    (l.map F).prod = ∏ i : Fin m, F (l[i.val]'(by rw [hl]; exact i.isLt)) := by
  subst m
  exact (Fin.prod_univ_fun_getElem l F).symm

theorem list_forall_getElem_of_length {α : Type*} (l : List α) (m : ℕ) (hl : l.length = m)
    (P : α → Prop) :
    (∀ a ∈ l, P a) ↔ ∀ i : Fin m, P (l[i.val]'(by rw [hl]; exact i.isLt)) := by
  constructor
  · intro h i
    exact h _ (List.getElem_mem _)
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hm : i < m := by rwa [hl] at hi
    exact h ⟨i, hm⟩

noncomputable def WordFourierParameters.uniform (n : ℕ) (profile : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : WordFourierParameters n where
  scale := fun _ => X
  profile := profile
  lower := fun _ => lo
  upper := fun _ => hi
  lower_one := fun _ => hlo
  lower_upper := fun _ => hhi

theorem polynomialLeafProduct_indexed {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (ψ : ℝ → ℂ) (X lo hi : ℝ) (x : σ → ℤ) :
    polynomialLeafProduct (template.weightedLeaves t hn .prime) ψ X lo hi x =
      (if ∀ i, (template.leafAt t hn i).formula.realValue x / X ∈ Set.Icc lo hi then 1 else 0) *
        ∏ i, normalizedFourierProfile ψ
          (if (template.leafAt t hn i).positive then ((template.leafAt t hn i).frequency : ℝ)
            else -((template.leafAt t hn i).frequency : ℝ))
          ((template.leafAt t hn i).formula.realValue x / X) := by
  rw [polynomialLeafProduct, list_prod_complex_gate (template.weightedLeaves t hn .prime)
    (fun z : WeightedWordLeaf σ => z.formula.realValue x / X ∈ Set.Icc lo hi)
    (fun z => normalizedFourierProfile ψ (if z.positive then (z.frequency : ℝ) else -(z.frequency : ℝ))
      (z.formula.realValue x / X))]
  simp only [list_forall_getElem_of_length _ (2 ^ n) (template.weightedLeaves_length t hn .prime)]
  rw [list_prod_getElem_of_length _ (2 ^ n) (template.weightedLeaves_length t hn .prime)]
  rfl

/-- This equality derives the coefficient on natural assignments from its support
and Fourier reconstruction. -/
theorem WordFourierParameters.uniform_coefficient {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (profile : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (x : σ → ℕ) :
    (WordFourierParameters.uniform n profile X lo hi hlo hhi).coefficient
      template t hn (fun i => (x i : ℤ)) =
      if ValidTransferHistory (wordTransferSystem σ) n (template.state x) t then
        polynomialLeafProduct (template.weightedLeaves t hn .prime) profile X lo hi (fun i => (x i : ℤ))
      else 0 := by
  rw [polynomialLeafProduct_indexed]
  simp only [coefficient, uniform, frequency, template.guardAt_valid_iff t hn x]
  split_ifs <;> simp_all

/-- Exact identification with the weight used in the original amplitude. -/
theorem WordTransferTemplate.recursive_weight_coefficient {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) :
    recursiveTransferWeight (wordTransferSystem σ)
      (fun τ v => (if (wordTransferLeafValue τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((wordTransferLeafValue τ : ℝ) / X))
      (fun _ _ _ _ => 1) n (template.state x) t =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).coefficient
        template t hn (fun i => (x i : ℤ)) := by
  rw [WordFourierParameters.uniform_coefficient,
    template.recursive_weight_polynomial_leaves x t hn ψ hreal X lo hi]

end Ostmann

end OAI
