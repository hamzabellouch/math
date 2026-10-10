import OAI.NumberTheory.Ostmann.Construction.WeightedWordLeaves
import OAI.NumberTheory.Ostmann.Construction.WordTransferFormulaBounds

namespace OAI

/-! # Exact Fourier factors and polynomial budgets of a concrete word history -/

namespace Ostmann

open scoped SchwartzMap FourierTransform ComplexConjugate Classical

/-- Rational reconstruction and the real polynomial specialization agree,
including away from the integral support. -/
theorem HistoryFormula.realValue_ratCast {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) :
    F.realValue x = (F.value (fun i => (x i : ℚ)) : ℝ) := by
  have hr : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℝ) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) F.cleared.numerator := by
    simpa [Int.castRingHom] using
      MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℝ) F.cleared.numerator
  have hq : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.cleared.numerator := by
    simpa [Int.castRingHom] using
      MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.cleared.numerator
  simp only [realValue, value, ClearedHistoryValue.eval, ← hr, ← hq,
    Rat.cast_div, Rat.cast_intCast]

noncomputable def WeightedWordLeaf.fourierValue {σ : Type*}
    (ψ : ℝ → ℂ) (X : ℝ) (x : σ → ℤ) (z : WeightedWordLeaf σ) : ℂ :=
  normalizedFourierProfile ψ (if z.positive then (z.frequency : ℝ) else -(z.frequency : ℝ))
    (z.formula.realValue x / X)

noncomputable def evaluatedFourierValue (ψ : ℝ → ℂ) (X : ℝ) (z : Bool × ℤ × ℚ) : ℂ :=
  normalizedFourierProfile ψ (if z.1 then (z.2.1 : ℝ) else -(z.2.1 : ℝ)) ((z.2.2 : ℝ) / X)

/-- The Fourier product uses the actual terminal word products and every
conjugation sign of the original frequency tree. -/
theorem WordTransferTemplate.fourier_product {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t)
    (ψ : ℝ → ℂ) (X : ℝ) :
    ((template.weightedLeaves t hn .prime).map
      (WeightedWordLeaf.fourierValue ψ X (fun i => (x i : ℤ)))).prod =
    ((transferLeafList (wordTransferSystem σ) n (template.state x) t).map (fun z =>
      normalizedFourierProfile ψ (if z.2 then (z.1.2 : ℝ) else -(z.1.2 : ℝ))
        ((wordTransferLeafValue z.1.1 : ℝ) / X))).prod := by
  have he := template.weightedLeaves_value x t hn .prime (fun i => (x i : ℚ))
    (by intro i; simp only [HistoryFormula.value_prime]) hv
  have hh := congrArg (fun l => (l.map (evaluatedFourierValue ψ X)).prod) he
  simp only [List.map_map, Function.comp_def, evaluatedFourierValue,
    WeightedWordLeaf.evaluate, evaluatedTransferLeaf, Rat.cast_natCast] at hh
  change ((template.weightedLeaves t hn .prime).map (fun z =>
    normalizedFourierProfile ψ (if z.positive then (z.frequency : ℝ) else -(z.frequency : ℝ))
      (z.formula.realValue (fun i => (x i : ℤ)) / X))).prod = _
  simp only [HistoryFormula.realValue_ratCast, Int.cast_natCast]
  exact hh

/-- This identifies the original recursive weight with the constructed
polynomial leaves; all real arithmetic and bin cutoffs stay in its exact support. -/
theorem WordTransferTemplate.recursive_fourier_weight {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y) (X : ℝ)
    (leafCutoff : WordTransferState σ → ℤ → ℝ)
    (cutoff : WordTransferState σ → ℤ → ℤ → ℤ → ℝ) :
    recursiveTransferWeight (wordTransferSystem σ)
      (fun τ v => (leafCutoff τ v : ℂ) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v
        ((wordTransferLeafValue τ : ℝ) / X)) cutoff n (template.state x) t =
      (recursiveSupportFactor (wordTransferSystem σ) leafCutoff cutoff n (template.state x) t : ℂ) *
        ((template.weightedLeaves t hn .prime).map
          (WeightedWordLeaf.fourierValue (𝓕 ψ : 𝓢(ℝ, ℂ)) X (fun i => (x i : ℤ)))).prod := by
  rw [recursiveFourierWeight_leaf_expansion, template.fourier_product x t hn hv]
  exact hreal

/-- The frequency-carrying leaves inherit the derived substitution budget. -/
theorem WordTransferTemplate.weightedLeaves_cost {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) :
    ∀ z ∈ template.weightedLeaves t hn .prime, z.formula.cost ≤ B ^ (n + 1) := by
  intro z hz
  have hmem : z.toSignedFormula ∈ (template.branching t hn).formulaLeaves .prime := by
    rw [← template.weightedLeaves_projection t hn .prime]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  simpa only [Nat.one_mul, WeightedWordLeaf.toSignedFormula] using
    (template.branching_formula_cost t hn B 1 hB (by omega) hwords .prime
      (fun _ => le_rfl)).1 z.toSignedFormula hmem

end Ostmann

end OAI
