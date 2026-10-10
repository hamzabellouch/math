import Mathlib
import OAI.Computability.VertexCover.Repetition.ProfileCorrection
import OAI.Computability.VertexCover.Repetition.SelectedCommon

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

theorem firstMarginal_totalVariation_le (r t : X × Y → ℝ) :
    totalVariation (firstMarginal r) (firstMarginal t) ≤ totalVariation r t := by
  unfold totalVariation firstMarginal
  simp_rw [← Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => Finset.abs_sum_le_sum_abs (fun y : Y => r (x,y)-t (x,y)) Finset.univ)
  rw [Fintype.sum_prod_type]
  linarith

def leftCommonMarginal (p : S × (X × Y) → ℝ) : X × S → ℝ :=
  fun z => ∑ y, p (z.2,(z.1,y))

def leftCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : X → S → ℝ :=
  conditionalKernel (leftCommonMarginal p) fallback

def swapSeedLeft : (X × (S × Y)) ≃ (S × (X × Y)) where
  toFun z := (z.2.1,(z.1,z.2.2))
  invFun z := (z.2.1,(z.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem leftCommonMarginal_isProbability (p : S × (X × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (leftCommonMarginal p) := by
  exact ProfileCorrection.seedQuestionMarginal_isProbability
    (fun z => p (swapSeedLeft z)) (isProbability_comp_equiv swapSeedLeft p hp)

theorem leftCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (x : X) :
    IsProbability (leftCommonProfile p fallback x) :=
  conditionalKernel_isProbability _ _ (leftCommonMarginal_isProbability p hp) hf x

theorem leftCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1) ≤
      totalVariation p (leftRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapSeedLeft (S := S) (X := X) (Y := Y)
  let p' : X × (S × Y) → ℝ := fun z => p (e z)
  have h := ProfileCorrection.left_profile_correction p' μ.weight fallback
    (μ.pushforward Prod.snd).weight
    (isProbability_comp_equiv e p hp) (gameLaw_isProbability μ) hf
    (gameLaw_isProbability (μ.pushforward Prod.snd))
  have hs : ProfileCorrection.seedQuestionMarginal p' = leftCommonMarginal p := rfl
  have hc : (fun z : X × (S × Y) => ProfileCorrection.seedQuestionMarginal p' (z.1,z.2.1) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2) =
      fun z => leftRevealModel μ p (e z) := by
    funext z
    change (∑ y, p (z.2.1,(z.1,y))) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2 =
      (∑ y, p (z.2.1,(z.1,y))) *
        (revealProfile μ (Sum.inl z.1)).weight (z.1,z.2.2)
    rw [revealProfile_inl_diagonal]
  have hd : (fun z : X × (S × Y) => μ.weight (z.1,z.2.2) *
      conditionalKernel (ProfileCorrection.seedQuestionMarginal p') fallback z.1 z.2.1) =
      fun z => μ.weight (e z).2 * leftCommonProfile p fallback (e z).2.1 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (leftRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1)] at h
  have hm : firstMarginal p' = firstMarginal (secondMarginal p) := by
    funext x
    simp only [firstMarginal, secondMarginal, Fintype.sum_prod_type, p', e, swapSeedLeft]
    exact Finset.sum_comm
  rw [hm] at h
  exact h.trans (add_le_add le_rfl (firstMarginal_totalVariation_le (secondMarginal p) μ.weight))

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
