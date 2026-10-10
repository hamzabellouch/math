import Mathlib
import OAI.Computability.VertexCover.Repetition.DistributionMaps
import OAI.Computability.VertexCover.Repetition.ProfileBounds

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
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def swapQuestionEndpoints : (S × (Y × X)) ≃ (S × (X × Y)) where
  toFun z := (z.1,(z.2.2,z.2.1))
  invFun z := (z.1,(z.2.2,z.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rightCommonMarginal (p : S × (X × Y) → ℝ) : Y × S → ℝ :=
  fun z => ∑ x, p (z.2,(x,z.1))

def rightCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : Y → S → ℝ :=
  conditionalKernel (rightCommonMarginal p) fallback

theorem rightCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (y : Y) :
    IsProbability (rightCommonProfile p fallback y) :=
  leftCommonProfile_isProbability (fun z => p (swapQuestionEndpoints z)) fallback
    (isProbability_comp_equiv swapQuestionEndpoints p hp) hf y

theorem swap_question_pushforward_snd (μ : FiniteDistribution (X × Y)) :
    ((μ.transport (Equiv.prodComm X Y)).pushforward Prod.snd) = μ.pushforward Prod.fst := by
  rw [FiniteDistribution.transport_eq_pushforward, FiniteDistribution.pushforward_comp]
  rfl

omit [Fintype S] in
theorem leftRevealModel_swap [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (z : S × (Y × X)) :
    leftRevealModel (μ.transport (Equiv.prodComm X Y))
      (fun z => p (swapQuestionEndpoints z)) z = rightRevealModel μ p (swapQuestionEndpoints z) := by
  rcases z with ⟨s,y,x⟩
  change (∑ x', p (s,(x',y))) *
      (revealProfile (μ.transport (Equiv.prodComm X Y)) (Sum.inl y)).weight (y,x) =
    (∑ x', p (s,(x',y))) * (revealProfile μ (Sum.inr y)).weight (x,y)
  rw [revealProfile_inl_diagonal, revealProfile_inr_diagonal, swap_question_pushforward_snd]

theorem rightCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1) ≤
      totalVariation p (rightRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapQuestionEndpoints (S := S) (X := X) (Y := Y)
  let p' : S × (Y × X) → ℝ := fun z => p (e z)
  let μ' := μ.transport (Equiv.prodComm X Y)
  have h := leftCommonProfile_error p' μ' fallback (isProbability_comp_equiv e p hp) hf
  have hc : leftRevealModel μ' p' = fun z => rightRevealModel μ p (e z) := by
    funext z
    exact leftRevealModel_swap p μ z
  have hd : (fun z : S × (Y × X) => μ'.weight z.2 * leftCommonProfile p' fallback z.2.1 z.1) =
      fun z => μ.weight (e z).2 * rightCommonProfile p fallback (e z).2.2 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (rightRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1)] at h
  have hm : totalVariation (secondMarginal p') μ'.weight =
      totalVariation (secondMarginal p) μ.weight := by
    change totalVariation (fun yx => secondMarginal p ((Equiv.prodComm Y X) yx))
      (fun yx => μ.weight ((Equiv.prodComm Y X) yx)) = _
    exact totalVariation_comp_equiv (Equiv.prodComm Y X) _ _
  rw [hm] at h
  exact h

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
