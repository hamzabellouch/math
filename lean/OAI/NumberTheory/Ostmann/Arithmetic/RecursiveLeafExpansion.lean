import OAI.NumberTheory.Ostmann.Construction.RecursiveTransferWeight
import OAI.NumberTheory.Ostmann.Construction.HistoryFourierConjugation

namespace OAI

/-! # The exact signed leaves and real support factor of a recursive history -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform Classical

/-- The flag records the conjugations accumulated from right branches. -/
noncomputable def transferLeafList {State : Type*} (sys : TransferHistorySystem State) :
    (n : ℕ) → State → FrequencyTree ℤ n → List ((State × ℤ) × Bool)
  | 0, σ, v => [((σ, v), true)]
  | n + 1, σ, t =>
      let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      transferLeafList sys n (sys.leftState σ P) t.2.1 ++
        (transferLeafList sys n (sys.rightState σ P) t.2.2).map (fun z => (z.1, !z.2))

theorem transferLeafList_length {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    (transferLeafList sys n σ t).length = 2 ^ n := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [transferLeafList, List.length_append, List.length_map, ih]
    rw [pow_succ]
    omega

noncomputable def signedLeafValue {State : Type*} (F : State → ℤ → ℂ)
    (z : (State × ℤ) × Bool) : ℂ :=
  if z.2 then F z.1.1 z.1.2 else conj (F z.1.1 z.1.2)

theorem signedLeafValue_flip {State : Type*} (F : State → ℤ → ℂ)
    (z : (State × ℤ) × Bool) :
    signedLeafValue F (z.1, !z.2) = conj (signedLeafValue F z) := by
  rcases z with ⟨⟨σ, v⟩, b⟩
  cases b <;> simp [signedLeafValue]

theorem signedLeafProduct_flip {State : Type*} (F : State → ℤ → ℂ)
    (l : List ((State × ℤ) × Bool)) :
    ((l.map (fun z => (z.1, !z.2))).map (signedLeafValue F)).prod =
      conj ((l.map (signedLeafValue F)).prod) := by
  induction l with
  | nil => simp
  | cons z l ih =>
    simp only [List.map_cons, List.prod_cons, signedLeafValue_flip, ih, map_mul]

/-- Leaf bins and all intermediate arithmetic/range gates are real. They
remain real under every conjugation in the frequency tree. -/
noncomputable def recursiveSupportFactor {State : Type*} (sys : TransferHistorySystem State)
    (leafCutoff : State → ℤ → ℝ) (cutoff : State → ℤ → ℤ → ℤ → ℝ) :
    (n : ℕ) → State → FrequencyTree ℤ n → ℝ
  | 0, σ, v => leafCutoff σ v
  | n + 1, σ, t =>
      let v := frequencyRoot n t.2.1
      let w := frequencyRoot n t.2.2
      let P := historyPivot sys σ t.1 v w
      if ValidTransferNode sys σ t.1 v w P then
        cutoff σ t.1 v w * recursiveSupportFactor sys leafCutoff cutoff n (sys.leftState σ P) t.2.1 *
          recursiveSupportFactor sys leafCutoff cutoff n (sys.rightState σ P) t.2.2
      else 0

/-- This equality uses the original recursive weight, including its actual
reconstructed pivots and its validity tests. -/
theorem recursiveTransferWeight_leaf_expansion {State : Type*}
    (sys : TransferHistorySystem State) (F : State → ℤ → ℂ)
    (leafCutoff : State → ℤ → ℝ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight sys (fun σ v => (leafCutoff σ v : ℂ) * F σ v) cutoff n σ t =
      (recursiveSupportFactor sys leafCutoff cutoff n σ t : ℂ) *
        ((transferLeafList sys n σ t).map (signedLeafValue F)).prod := by
  induction n generalizing σ with
  | zero => simp [recursiveTransferWeight, recursiveSupportFactor, transferLeafList, signedLeafValue]
  | succ n ih =>
    let v := frequencyRoot n t.2.1
    let w := frequencyRoot n t.2.2
    let P := historyPivot sys σ t.1 v w
    by_cases hp : ValidTransferNode sys σ t.1 v w P
    · rw [recursiveTransferWeight_node sys _ cutoff n σ t P hp]
      simp only [recursiveSupportFactor, transferLeafList, v, w, P, hp, ite_true,
        List.map_append, List.prod_append, signedLeafProduct_flip, ih, Complex.star_def, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    · simp only [recursiveTransferWeight, recursiveSupportFactor, v, w, P, hp, ite_false,
        Complex.ofReal_zero, zero_mul]

/-- Every leaf conjugation is absorbed into its frequency; the Fourier
profile remains the same fixed Schwartz function throughout the tree. -/
theorem recursiveFourierWeight_leaf_expansion {State : Type*}
    (sys : TransferHistorySystem State) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (scale : State → ℝ)
    (leafCutoff : State → ℤ → ℝ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight sys
      (fun σ v => (leafCutoff σ v : ℂ) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v (scale σ))
      cutoff n σ t =
      (recursiveSupportFactor sys leafCutoff cutoff n σ t : ℂ) *
        ((transferLeafList sys n σ t).map (fun z =>
          normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ))
            (if z.2 then (z.1.2 : ℝ) else -(z.1.2 : ℝ)) (scale z.1.1))).prod := by
  rw [recursiveTransferWeight_leaf_expansion]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro z _
  rcases z with ⟨⟨τ, v⟩, b⟩
  cases b
  · exact normalizedFourierProfile_fourier_conj ψ hreal v (scale τ)
  · rfl

end Ostmann

end OAI
