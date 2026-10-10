import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityMixture
import OAI.Combinatorics.ContingencyTables.Counting.CompanionWarmStart

namespace OAI

/-! # Independent initial cell choices give the literal companion law

The finite rational law is the product of the uniform-size subset laws.
Encoding a choice as its paired transversal yields exactly the initial
law of the companion's factorial lift, with its actual free-completion
normalizer cancelled.
-/

namespace ContingencyTables.InitialFactorialLaw

open CommonBasesFPRAS ResidualMixture FirstSuccess TwoLiftStates LabelledFactorial
open InitialTransversals FixedCardinalityMixture CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {C : Type*} [Fintype C] (b : C → ℕ)

def choiceLaw : RationalLaw ((c : C) → Finset (Fin (b c))) where
  mass S := ∏ c,(localLaw (b c)).mass (S c)
  nonnegative S := Finset.prod_nonneg (fun c _ => (localLaw (b c)).nonnegative (S c))
  total := by
    rw [←Fintype.prod_sum]
    simp only [(localLaw _).total,Finset.prod_const_one]

theorem choiceLaw_mass_cast (S : (c : C) → Finset (Fin (b c))) :
    ((choiceLaw b).mass S:ℝ)=
      (∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c))/(∏ c,((b c:ℝ)+1)) := by
  change ((∏ c,(localLaw (b c)).mass (S c):ℚ):ℝ)=_
  rw [Rat.cast_prod]
  simp_rw [localLaw_mass_cast]
  exact Finset.prod_div_distrib
    (fun c : C => InitialLocalChoices.localWeight (b c) 0 0 (S c))
    (fun c : C => (b c:ℝ)+1)

def plainLaw : RationalLaw {S : Set (Copy b×Bool) // PlainState pairs S} :=
  equivLaw (plainEquivChoices b).symm (choiceLaw b)

theorem plainLaw_mass_cast (S : {S : Set (Copy b×Bool) // PlainState pairs S}) :
    ((plainLaw b).mass S:ℝ)=
      (∏ c,InitialLocalChoices.localWeight (b c) 0 0 ((plainEquivChoices b S) c))/
        (∏ c,((b c:ℝ)+1)) :=
  choiceLaw_mass_cast b (plainEquivChoices b S)

theorem plainLaw_lift (M : ℝ) (hM : 0<M)
    (S : {S : Set (Copy b×Bool) // PlainState pairs S}) :
    ((plainLaw b).mass S:ℝ)=
      firstLift (group (cell b)) (fun _ => M) (InitialTransversals.denominator b) S.val/
        (M*∏ c,((b c:ℝ)+1)) := by
  let choices := plainEquivChoices b S
  have he : encode b choices=S.val :=
    congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply S)
  rw [←he,firstLift_encode,plainLaw_mass_cast]
  exact (mul_div_mul_left _ _ (ne_of_gt hM)).symm

variable {I J : Type*} [Fintype I] [Fintype J]

def companionLaw (A : Instance I J) :
    RationalLaw {S : Set (Labels A×Bool) // PlainState pairs S} :=
  plainLaw (fun s : SmallCell A => A.b s.val.1 s.val.2)

/-- No abstract initialization hypothesis: the rational product law is
the actual phase-zero law of the given bounded-table instance. -/
theorem companionLaw_mass (A : Instance I J)
    (S : {S : Set (Labels A×Bool) // PlainState pairs S}) :
    ((companionLaw A).mass S:ℝ)=CompanionWarmStart.law A 0 S.val := by
  have hM : 0<CompanionInitialization.freeTotal A := by
    apply Finset.prod_pos
    intro a _
    exact Nat.cast_pos.mpr (Nat.succ_pos _)
  have h := plainLaw_lift (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (CompanionInitialization.freeTotal A) hM S
  have hf : f A 0=firstLift (group (labelCell A))
      (fun _ => CompanionInitialization.freeTotal A)
      (CompanionFactorialApplication.denominator A) := by
    funext T
    unfold f firstLift
    rw [CompanionInitialization.h_zero]
  change ((plainLaw _).mass S:ℝ)=_
  unfold CompanionWarmStart.law CompanionWarmStart.total CompanionAnnealing.weight
  simp only [Nat.cast_zero,zero_div]
  rw [CompanionInitialization.total_zero,hf,CompanionInitialization.denominator_eq]
  exact h

end
end ContingencyTables.InitialFactorialLaw

end OAI
