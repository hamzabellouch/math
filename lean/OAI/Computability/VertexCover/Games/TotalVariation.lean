import Mathlib
import OAI.Computability.VertexCover.Games.Basic
import OAI.Computability.VertexCover.Information.Finite

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

namespace UniqueGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

def totalVariation (μ ν : FiniteDistribution Ω) : ℝ :=
  (∑ x, |μ.weight x - ν.weight x|) / 2

theorem totalVariation_nonnegative (μ ν : FiniteDistribution Ω) :
    0 ≤ μ.totalVariation ν :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem totalVariation_comm (μ ν : FiniteDistribution Ω) :
    μ.totalVariation ν = ν.totalVariation μ := by
  unfold totalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_abs_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    |μ.probability event - ν.probability event| ≤ μ.totalVariation ν := by
  apply abs_le.mpr
  constructor
  · have h := ν.probability_sub_le_totalVariation μ event
    rw [totalVariation_comm] at h
    linarith
  · exact μ.probability_sub_le_totalVariation ν event

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end
end UniqueGames.Foundations.Games.FiniteDistribution

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
