import OAI.NumberTheory.Ostmann.Construction.WordRangeReplay
import OAI.NumberTheory.Ostmann.Construction.WordTransferUniformCoefficient

namespace OAI

/-! # The recursive weight with every intermediate range retained -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def WordRangeDecoration.weight {σ : Type*}
    (leaf : WordTransferState σ → ℤ → ℂ) :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (σ → ℕ) → FrequencyTree ℤ n → ℂ
  | 0, .leaf ranges, .leaf word, x, v =>
      (if ∀ r ∈ ranges, r.Holds x then 1 else 0) * leaf ((WordTransferTemplate.leaf word).state x) v
  | n + 1, .node ranges L R, .node d l r, x, t =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      if ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P then
        (if ∀ q ∈ ranges, q.Holds x then 1 else 0) *
          L.weight leaf l (Function.update x d.target P) t.2.1 *
          star (R.weight leaf r (Function.update x d.target P) t.2.2)
      else 0

theorem WordRangeDecoration.weight_eq {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (leaf : WordTransferState σ → ℤ → ℂ) (x : σ → ℕ) (t : FrequencyTree ℤ n) :
    D.weight leaf template x t =
      (if D.ValidAt template x t then 1 else 0) *
        recursiveTransferWeight (wordTransferSystem σ) leaf (fun _ _ _ _ => 1) n (template.state x) t := by
  induction template generalizing x with
  | leaf word =>
    cases D
    simp only [weight, ValidAt, recursiveTransferWeight]
    congr 1
    congr 1
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      by_cases hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
      · rw [recursiveTransferWeight_node _ _ _ n _ t P hp]
        simp only [weight, ValidAt, hp, ite_true, P, ihL, ihR, Complex.ofReal_one, one_mul,
          wordTransferLeftState_node, wordTransferRightState_node]
        split_ifs <;> simp_all
      · simp only [weight, recursiveTransferWeight, P, hp, ite_false, mul_zero]

noncomputable def WordFourierParameters.rangedCoefficient {σ : Type*} {n : ℕ}
    (p : WordFourierParameters n) (D : WordRangeDecoration σ n)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) : ℂ :=
  (if ∀ r ∈ D.formulas template t ht .prime, r.Holds x then 1 else 0) * p.coefficient template t ht x

/-- The polynomial range coefficient is the literal recursive weight with
all bins at every node, not a replacement support assumption. -/
theorem WordRangeDecoration.weight_coefficient {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (x : σ → ℕ) (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) :
    D.weight
      (fun τ v => (if (wordTransferLeafValue τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((wordTransferLeafValue τ : ℝ) / X))
      template x t =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).rangedCoefficient
        D template t ht (fun i => (x i : ℤ)) := by
  rw [weight_eq, template.recursive_weight_coefficient x t ht ψ hreal X lo hi hlo hhi,
    WordFourierParameters.rangedCoefficient]
  by_cases hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t
  · have he := D.formulas_iff template t ht .prime (fun i => (x i : ℤ)) x
      (fun i => by simp only [HistoryFormula.value_prime, Int.cast_natCast]) hv
    simp only [he]
  · rw [WordFourierParameters.uniform_coefficient]
    simp only [hv, ite_false, mul_zero]

end Ostmann

end OAI
