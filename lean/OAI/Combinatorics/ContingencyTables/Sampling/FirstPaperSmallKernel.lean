import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallMixing
import OAI.Combinatorics.ContingencyTables.Transport.RationalChainCast

namespace OAI

/-! # The exact rational law of the actual small-state completion chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def smallProposalRat (d : ℕ) : ℚ := 1/(2:ℚ)^Nat.clog 2 (32*d^2)

noncomputable def smallMoveRat (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) : ℚ :=
  if physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x y then
    smallProposalRat (dimensionAllowance (I := I) (J := J))*
      (acceptedCount (referenceRows r c _ _ (stateCapacity r c) i₀)
        (referenceColumns r c _ _ (stateCapacity r c) j₀) x y:ℚ)/
      (blockCount (referenceRows r c _ _ (stateCapacity r c) i₀)
        (referenceColumns r c _ _ (stateCapacity r c) j₀) x:ℚ)
  else 0

noncomputable def smallTransitionRat (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) : ℚ :=
  smallMoveRat r c i₀ j₀ x y+if x=y then 1-∑ z,smallMoveRat r c i₀ j₀ x z else 0

lemma smallMoveRat_cast (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) :
    (smallMoveRat r c i₀ j₀ x y:ℝ)=
      completionMove (referenceRows r c _ _ (stateCapacity r c) i₀)
        (referenceColumns r c _ _ (stateCapacity r c) j₀)
        (physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c))
        (smallProposal (dimensionAllowance (I := I) (J := J))) x y := by
  unfold smallMoveRat completionMove
  split_ifs
  · simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,smallProposalRat,smallProposal,
      Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  · exact Rat.cast_zero

lemma smallTransitionRat_cast (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) :
    (smallTransitionRat r c i₀ j₀ x y:ℝ)=(paperSmallChain r c i₀ j₀).P x y := by
  unfold smallTransitionRat
  dsimp only [paperSmallChain,completionChain,FiniteChain.ofMoves]
  by_cases hxy : x=y <;>
    simp only [hxy,ite_true,ite_false,Rat.cast_add,Rat.cast_sub,Rat.cast_sum,
      Rat.cast_one,Rat.cast_zero,smallMoveRat_cast]

noncomputable def smallTransitionLaw (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) : RationalLaw (PaperStates r c) where
  mass := smallTransitionRat r c i₀ j₀ x
  nonnegative := fun y => by
    have h := (paperSmallChain r c i₀ j₀).nonnegative x y
    rw [← smallTransitionRat_cast] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum,smallTransitionRat_cast,Rat.cast_one]
    exact (paperSmallChain r c i₀ j₀).stochastic x

lemma smallTransitionLaw_mass_ne (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x y : PaperStates r c) (hxy : x≠y) :
    (smallTransitionLaw r c i₀ j₀ x).mass y=smallMoveRat r c i₀ j₀ x y := by
  change smallTransitionRat r c i₀ j₀ x y=_
  simp only [smallTransitionRat,hxy,ite_false,add_zero]

noncomputable def smallWalkLaw (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (x : PaperStates r c) (n : ℕ) : RationalLaw (PaperStates r c) :=
  walkLaw (smallTransitionLaw r c i₀ j₀) x n

lemma smallWalkLaw_cast (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (n : ℕ) (x y : PaperStates r c) :
    ((smallWalkLaw r c i₀ j₀ x n).mass y:ℝ)=
      ((paperSmallChain r c i₀ j₀).kernel.power n).P x y := by
  exact walkLaw_cast_kernel (smallTransitionLaw r c i₀ j₀) (paperSmallChain r c i₀ j₀)
    (smallTransitionRat_cast r c i₀ j₀) n x y

end ContingencyTables.SmallGraphProfiles

end OAI
