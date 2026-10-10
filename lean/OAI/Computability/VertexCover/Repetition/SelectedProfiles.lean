import Mathlib
import OAI.Computability.VertexCover.Repetition.RightProfileBounds

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem finiteDistribution_nonempty {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    Nonempty A := by
  have hsum : (∑ a, μ.weight a) ≠ 0 := by rw [μ.normalized]; norm_num
  obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨a⟩

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedProfileFallback (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).pushforward Prod.fst

def selectedLeftProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (x : Q₁) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (leftCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight x)
    (leftCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) x)

def selectedRightProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (y : Q₂) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (rightCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight y)
    (rightCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) y)

def selectedLeftProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

def selectedRightProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

theorem selectedLeftProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedLeftProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  leftCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

theorem selectedRightProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedRightProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  rightCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

def selectedSamplingTarget (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Q₁ × Q₂) × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)

theorem selectedSamplingTarget_left_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedLeftProfile G strategy selected positive j z.1.1).weight z.2) =
      selectedLeftProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

theorem selectedSamplingTarget_right_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedRightProfile G strategy selected positive j z.1.2).weight z.2) =
      selectedRightProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
