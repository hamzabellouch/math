import OAI.NumberTheory.Ostmann.Construction.HistoryCoefficientData
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedWordCoprimality

namespace OAI

/-! # Building the history coefficient from the original intermediate words -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

theorem reconstructedWordFormula_realValue {σ : Type*} (steps : List (HistoryPivotStep σ))
    (stage : ℕ) (word : List σ) (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x) :
    (reconstructedWordFormula steps stage word).realValue x =
      ((word.map (reconstructIntegers (steps.take stage) x)).prod : ℤ) :=
  (reconstructedWordFormula steps stage word).cleared.real_value_of_integer x _
    (reconstructedWordFormula_value steps stage word x hx)

noncomputable def HistoryCoefficientData.ofWords {σ : Type*} {n t : ℕ}
    (steps : List (HistoryPivotStep σ)) (units : Fin steps.length → ℕ)
    (leafStage : Fin n → ℕ) (leafWord : Fin n → List σ)
    (rangeStage : Fin t → ℕ) (rangeWord : Fin t → List σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (glo ghi : Fin t → ℝ) :
    HistoryCoefficientData σ where
  leafCount := n
  rangeCount := t
  steps := steps
  units := units
  leaves := fun j => reconstructedWordFormula steps (leafStage j) (leafWord j)
  ranges := fun j => reconstructedWordFormula steps (rangeStage j) (rangeWord j)
  scale := X
  fourier := ψ
  frequency := v
  lower := lo
  upper := hi
  lower_one := hlo
  lower_upper := hhi
  rangeLower := glo
  rangeUpper := ghi

theorem HistoryCoefficientData.ofWords_complexity {σ : Type*} {n t : ℕ}
    (steps : List (HistoryPivotStep σ)) (units : Fin steps.length → ℕ)
    (leafStage : Fin n → ℕ) (leafWord : Fin n → List σ)
    (rangeStage : Fin t → ℕ) (rangeWord : Fin t → List σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (glo ghi : Fin t → ℝ)
    (C W : ℕ) (hC : 1 ≤ C)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C)
    (hleaf : ∀ j, (leafWord j).length ≤ W) (hrange : ∀ j, (rangeWord j).length ≤ W) :
    (HistoryCoefficientData.ofWords steps units leafStage leafWord rangeStage rangeWord
      X ψ v lo hi hlo hhi glo ghi).complexity ≤
        (3 * n + 2 * t) * (W * C ^ steps.length + 1) := by
  have hb (stage : ℕ) (word : List σ) (hw : word.length ≤ W) :
      (reconstructedWordFormula steps stage word).cost ≤ W * C ^ steps.length + 1 :=
    (reconstructedWordFormula_cost steps stage word C hC hsize).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hw) 1)
  have hl : (∑ j : Fin n, (reconstructedWordFormula steps (leafStage j) (leafWord j)).cost) ≤
      n * (W * C ^ steps.length + 1) := by
    calc
      _ ≤ ∑ _j : Fin n, (W * C ^ steps.length + 1) :=
        Finset.sum_le_sum fun j _ => hb _ _ (hleaf j)
      _ = _ := by simp
  have hr : (∑ j : Fin t, (reconstructedWordFormula steps (rangeStage j) (rangeWord j)).cost) ≤
      t * (W * C ^ steps.length + 1) := by
    calc
      _ ≤ ∑ _j : Fin t, (W * C ^ steps.length + 1) :=
        Finset.sum_le_sum fun j _ => hb _ _ (hrange j)
      _ = _ := by simp
  dsimp only [HistoryCoefficientData.complexity, HistoryCoefficientData.ofWords]
  nlinarith

/-- On the exact integral support, all Fourier and bin arguments are the
original products after the specified prefix of pivot substitutions. -/
theorem HistoryCoefficientData.ofWords_value {σ : Type*} {n t : ℕ}
    (steps : List (HistoryPivotStep σ)) (units : Fin steps.length → ℕ)
    (leafStage : Fin n → ℕ) (leafWord : Fin n → List σ)
    (rangeStage : Fin t → ℕ) (rangeWord : Fin t → List σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (glo ghi : Fin t → ℝ)
    (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x) :
    (HistoryCoefficientData.ofWords steps units leafStage leafWord rangeStage rangeWord
      X ψ v lo hi hlo hhi glo ghi).value x =
      (if ∀ i, IsUnit ((reconstructedPivotAt steps x i : ℤ) : ZMod (units i)) then 1 else 0) *
      (if (∀ j, ((((rangeWord j).map (reconstructIntegers (steps.take (rangeStage j)) x)).prod : ℤ) : ℝ)
          ∈ Set.Icc (glo j) (ghi j)) ∧
        (∀ j, ((((leafWord j).map (reconstructIntegers (steps.take (leafStage j)) x)).prod : ℤ) : ℝ) / X j
          ∈ Set.Icc (lo j) (hi j)) then 1 else 0) *
      ∏ j, normalizedFourierProfile ψ (v j)
        (((((leafWord j).map (reconstructIntegers (steps.take (leafStage j)) x)).prod : ℤ) : ℝ) / X j) := by
  simp only [HistoryCoefficientData.value, HistoryCoefficientData.ofWords,
    globalHistoryCoefficient, globalHistoryArchCoefficient, hx, true_and,
    reconstructedWordFormula_realValue steps _ _ x hx]
  simp only [mul_assoc]
  rfl

end Ostmann

end OAI
