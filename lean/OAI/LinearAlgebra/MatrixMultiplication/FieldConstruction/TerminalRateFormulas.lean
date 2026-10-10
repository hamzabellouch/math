import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Sums
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ZeroLeafRateFormula
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Contractions

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldTerminalRates

open AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def initialRate (g : Shape) : ℝ :=
  Real.log (Contractions.coefficients[shapeMax g]?.getD 0 : ℝ)

def S0 : ℝ :=
  ((sortedInitial.filter (fun g => !positive g)).map
    (fun g => (initialLaw g : ℝ) * initialRate g)).sum

def S1 : ℝ :=
  (zeroSecond.map (fun t => (secondMass t : ℝ) * AllFieldZeroLeafRates.fourRate t)).sum

def secondLeafRate (t u : Shape) : ℝ :=
  if shapeMax u = 4 then 0
  else if shapeMax u = 3 then Real.log 10
  else if !positive u then
    binaryEntropyRate (binaryParameter t u) +
      2 * (1 - (binaryParameter t u : ℝ)) * Real.log 5
  else (2 - (binaryParameter t u : ℝ)) * Real.log 5

def S2 : ℝ :=
  (positiveSecond.map (fun t =>
    ((below t).map (fun u => (littleMass t u : ℝ) * secondLeafRate t u)).sum)).sum

def S : ℝ := (S0 + S1) + S2

private theorem four_shape_max_lt_five : ∀ u ∈ shapes 4, shapeMax u < 5 := by
  decide +kernel

private theorem four_zero_max : ∀ u ∈ shapes 4, positive u = false →
    shapeMax u = 2 ∨ shapeMax u = 3 ∨ shapeMax u = 4 := by
  decide +kernel

private theorem four_positive_max : ∀ u ∈ shapes 4, positive u = true →
    shapeMax u = 2 := by
  decide +kernel

theorem second_shapeMax_lt_five (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) : shapeMax u < 5 :=
  four_shape_max_lt_five u (stageB_children_size t ht u hu)

theorem secondLeafRate_zero (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (hz : positive u = false) :
    secondLeafRate t u = statisticRate (binaryParameter t u)
      ⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ := by
  rcases four_zero_max u (stageB_children_size t ht u hu) hz with h2 | h3 | h4
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 2 :=
      Fin.ext h2
    rw [hk, statisticRate_two]
    simp [secondLeafRate, h2, hz]
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 3 :=
      Fin.ext h3
    rw [hk, statisticRate_three]
    simp [secondLeafRate, h3]
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 4 :=
      Fin.ext h4
    rw [hk, statisticRate_four]
    simp [secondLeafRate, h4]

theorem secondLeafRate_positive (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (hp : positive u = true) :
    secondLeafRate t u = (2 - (binaryParameter t u : ℝ)) * Real.log 5 := by
  have hm := four_positive_max u (stageB_children_size t ht u hu) hp
  simp [secondLeafRate, hm, hp]

theorem secondLeafRate_builder_expression (t u : Shape) :
    secondLeafRate t u =
      if shapeMax u = 4 then 0
      else if shapeMax u = 3 then Real.log 10
      else if !positive u then
        (MatrixMultiplication.Foundation.entropyTerm (1 - (binaryParameter t u : ℝ)) +
          MatrixMultiplication.Foundation.entropyTerm (binaryParameter t u : ℝ) +
          (binaryParameter t u : ℝ) * Real.log 2) +
          ((1 - (binaryParameter t u : ℝ)) * 2) * Real.log 5
      else (2 - (binaryParameter t u : ℝ)) * Real.log 5 := by
  unfold secondLeafRate
  split_ifs <;> try rfl
  unfold binaryEntropyRate
  ring

private theorem list_filter_sum {A : Type*} (xs : List A) (p : A → Bool)
    (f : A → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

theorem initial_zero_history_rate (K : ℕ) :
    (∑ h : {h : Initial K // initialShape h ∉ positiveInitial},
      (initialAmount h.val : ℝ) * initialRate (initialShape h.val)) = (K : ℝ) * S0 := by
  calc
    _ = ∑ h : Initial K, if initialShape h ∉ positiveInitial then
        (initialAmount h : ℝ) * initialRate (initialShape h) else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype
        (p := fun h : Initial K => initialShape h ∉ positiveInitial)
        (Finset.univ.filter (fun h : Initial K => initialShape h ∉ positiveInitial))
        (by simp)
        (fun h : Initial K => (initialAmount h : ℝ) * initialRate (initialShape h))).symm
    _ = ∑ h : Initial K, (initialAmount h : ℝ) *
        (if initialShape h ∉ positiveInitial then initialRate (initialShape h) else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> simp
    _ = _ := by
      rw [initial_history_sum K
        (fun g => if g ∉ positiveInitial then initialRate g else 0), S0, list_filter_sum]
      apply congrArg (fun x : ℝ => (K : ℝ) * x)
      apply congrArg List.sum
      apply List.map_congr_left
      intro g hg
      cases hp : positive g <;> simp [positiveInitial, hg, hp]

end MatrixMultiplication.AllFieldTerminalRates

end

end OAI
