import OAI.Combinatorics.ContingencyTables.Rooted.RootedTraceWords
import OAI.Combinatorics.ContingencyTables.Rooted.RootedWarmStart
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTargetTrace

namespace OAI

/-! # Selected-root dyadic trace return and explicit warm cap estimates -/

namespace ContingencyTables.RootedTargetTrace

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTraceWords
open CompanionCappedReturn RootedAnnealing RootedWarmStart TwoLiftStates
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open CompanionTargetTrace (capSteps)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def actualTrace (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q) : FiniteChain (PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) := by
  letI := plainIndex_nonempty (pairs : List (CompanionRationalUpdates.Pair A))
    PairedLabels.fresh PairedLabels.cover
  exact (targetChain A R j hp w hw).traceChain (plainPredicate pairs)
    (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw)

theorem insideMass_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q) :
    (targetChain A R j hp w hw).insideMass (plainPredicate pairs)=
      total A R j/chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j) := by
  exact metropolis_insideMass pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j)
    (fun p q => by exact_mod_cast hw p q) (weight_positive A R j)

theorem actualTrace_pi (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    (actualTrace A R j hp w hw).π S=law A R j S.val.val := by
  have h := metropolisTrace_pi pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j)
    (fun p q => by exact_mod_cast hw p q) (weight_positive A R j) S
  exact h

theorem insideMass_lower (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ))) :
    1/(5*(Fintype.card (Labels A):ℝ)^2)≤
      (targetChain A R j hp w hw).insideMass (plainPredicate pairs) := by
  rw [insideMass_eq]
  have h := plain_mass_lower pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j)
    (fun p q => by exact_mod_cast hw p q) (weight_positive A R j) hgood.upper
  simpa only [PairedLabels.length,RootedWarmStart.total] using h

private theorem warm_div_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (U : ℝ) (hU : 0≤U) :
    U/(targetChain A R j hp w hw).insideMass (plainPredicate pairs)≤
      5*(Fintype.card (Labels A):ℝ)^2*U := by
  have hpR : (0:ℝ)<Fintype.card (Labels A) := by exact_mod_cast hp
  have hd : (0:ℝ)<5*(Fintype.card (Labels A):ℝ)^2 := by positivity
  have hm := insideMass_lower A R j hp w hw hgood
  have hm0 : 0<(targetChain A R j hp w hw).insideMass (plainPredicate pairs) :=
    lt_of_lt_of_le (one_div_pos.mpr hd) hm
  apply (div_le_iff₀ hm0).mpr
  have hone := (div_le_iff₀ hd).mp hm
  nlinarith [mul_le_mul_of_nonneg_left hone hU]

/-- Four-warm is the incoming bound after an adjacent-parameter restart.
More generally this holds for any nonnegative warmness coefficient. -/
theorem warm_cap_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (phi : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) → ℝ)
    (hphi : ∀ S,0≤phi S ∧ phi S≤1) (n : ℕ) (hn : 0<n)
    (nu : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A R j S.val.val) :
    (∑ S,nu S*|(targetChain A R j hp w hw).pathExpectation (n+1) S.val
      (fun xs => phi (returnDefault (plainPredicate pairs) S xs))-
        (∑ T,(targetChain A R j hp w hw).traceMatrix (plainPredicate pairs)
          (targetKilled A R j hp w hw) S T*phi T)|)≤
      (5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ) := by
  let := plainIndex_nonempty (pairs : List (CompanionRationalUpdates.Pair A))
    PairedLabels.fresh PairedLabels.cover
  have hh := warm_returnDefault_error (targetChain A R j hp w hw) (plainPredicate pairs)
    (targetKilled A R j hp w hw) (targetKilled_matches A R j hp w hw) phi hphi n hn nu hnu U
    (by
      intro S
      have hs := hwarm S
      rw [←actualTrace_pi A R j hp w hw S] at hs
      simpa only [actualTrace] using hs)
  exact hh.trans (div_le_div_of_nonneg_right (warm_div_mass A R j hp w hw hgood U hU)
    (Nat.cast_nonneg n))

theorem four_warm_cap_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (phi : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) → ℝ)
    (hphi : ∀ S,0≤phi S ∧ phi S≤1) (budget : ℕ) (hb : 0<budget)
    (nu : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hwarm : ∀ S,nu S≤4*law A R j S.val.val) :
    (∑ S,nu S*|(targetChain A R j hp w hw).pathExpectation (capSteps A budget+1) S.val
      (fun xs => phi (returnDefault (plainPredicate pairs) S xs))-
        (∑ T,(targetChain A R j hp w hw).traceMatrix (plainPredicate pairs)
          (targetKilled A R j hp w hw) S T*phi T)|)≤1/(budget:ℝ) := by
  have hn : 0<capSteps A budget := by
    unfold capSteps
    exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos hp)) hb
  have hh := warm_cap_error A R j hp w hw hgood phi hphi (capSteps A budget) hn nu hnu 4
    (by norm_num) hwarm
  have hpR : (Fintype.card (Labels A):ℝ)≠0 := by exact_mod_cast hp.ne'
  have hbR : (budget:ℝ)≠0 := by exact_mod_cast hb.ne'
  have he : (5*(Fintype.card (Labels A):ℝ)^2*4)/(capSteps A budget:ℝ)=1/(budget:ℝ) := by
    unfold capSteps
    push_cast
    field_simp [hpR,hbR]
    ring
  exact hh.trans_eq he

end
end ContingencyTables.RootedTargetTrace

end OAI
