import OAI.NumberTheory.Ostmann.Construction.WordTransferCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveSupportExpansion

namespace OAI

/-! # Identification of the original recursive weight with its polynomial leaves -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem recursiveTransferWeight_flat {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (n : ℕ) (x : State) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight sys leaf (fun _ _ _ _ => 1) n x t =
      if ValidTransferHistory sys n x t then
        ((transferLeafList sys n x t).map (signedLeafValue leaf)).prod else 0 := by
  have he := recursiveTransferWeight_leaf_expansion sys leaf (fun _ _ => 1) (fun _ _ _ _ => 1) n x t
  simp only [Complex.ofReal_one, one_mul] at he
  rw [recursiveSupportFactor_product] at he
  have hnode : transferNodeCutoff (fun (_ : State) (_ _ _ : ℤ) => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
  have hleaf : transferLeafCutoff (fun (_ : State) (_ : ℤ) => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
  rw [hnode, hleaf] at he
  simp only [List.map_const', List.prod_replicate, one_pow, mul_one] at he
  by_cases hv : ValidTransferHistory sys n x t
  · simpa only [hv, ite_true, Complex.ofReal_one, one_mul] using he
  · simpa only [hv, ite_false, Complex.ofReal_zero, zero_mul] using he

/-- Transport an arbitrary terminal factor through the actual frequency
and word-value reconstruction, retaining its conjugation flag. -/
theorem WordTransferTemplate.leaf_product_value {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t)
    (F : Bool → ℤ → ℝ → ℂ) :
    ((template.weightedLeaves t hn .prime).map (fun z =>
      F z.positive z.frequency (z.formula.realValue (fun i => (x i : ℤ))))).prod =
    ((transferLeafList (wordTransferSystem σ) n (template.state x) t).map (fun z =>
      F z.2 z.1.2 (wordTransferLeafValue z.1.1))).prod := by
  have he := template.weightedLeaves_value x t hn .prime (fun i => (x i : ℚ))
    (by intro i; simp only [HistoryFormula.value_prime]) hv
  have hh := congrArg (fun l => (l.map (fun z : Bool × ℤ × ℚ => F z.1 z.2.1 z.2.2)).prod) he
  simp only [List.map_map, Function.comp_def, WeightedWordLeaf.evaluate,
    evaluatedTransferLeaf, Rat.cast_natCast] at hh
  simpa only [HistoryFormula.realValue_ratCast, Int.cast_natCast] using hh

noncomputable def polynomialLeafProduct {σ : Type*}
    (leaves : List (WeightedWordLeaf σ)) (ψ : ℝ → ℂ) (X lo hi : ℝ) (x : σ → ℤ) : ℂ :=
  (leaves.map (fun z =>
    (if z.formula.realValue x / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile ψ (if z.positive then (z.frequency : ℝ) else -(z.frequency : ℝ))
        (z.formula.realValue x / X))).prod

/-- The original weight with its terminal bins equals the constructed
polynomial coefficient on precisely its original arithmetic support. -/
theorem WordTransferTemplate.recursive_weight_polynomial_leaves {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y) (X lo hi : ℝ) :
    recursiveTransferWeight (wordTransferSystem σ)
      (fun τ v => (if (wordTransferLeafValue τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((wordTransferLeafValue τ : ℝ) / X))
      (fun _ _ _ _ => 1) n (template.state x) t =
      if ValidTransferHistory (wordTransferSystem σ) n (template.state x) t then
        polynomialLeafProduct (template.weightedLeaves t hn .prime) (𝓕 ψ : 𝓢(ℝ, ℂ))
          X lo hi (fun i => (x i : ℤ)) else 0 := by
  rw [recursiveTransferWeight_flat]
  split_ifs with hv
  · rw [polynomialLeafProduct, template.leaf_product_value x t hn hv
      (fun b v r => (if r / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) (if b then (v : ℝ) else -(v : ℝ)) (r / X))]
    apply congrArg List.prod
    apply List.map_congr_left
    intro z _
    rcases z with ⟨⟨τ, v⟩, flag⟩
    cases flag
    · simp only [signedLeafValue, Bool.false_eq_true, ite_false, map_mul]
      rw [normalizedFourierProfile_fourier_conj ψ hreal]
      split_ifs <;> simp
    · rfl
  · rfl

end Ostmann

end OAI
