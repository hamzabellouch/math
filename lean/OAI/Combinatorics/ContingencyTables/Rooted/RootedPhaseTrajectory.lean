import OAI.Combinatorics.ContingencyTables.Rooted.RootedBooleanKernel
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseTrajectory

namespace OAI

/-! # The selected-root Boolean history has the exact source path comparison -/

namespace ContingencyTables.RootedPhaseTrajectory

open CommonBasesFPRAS RealKernelApproximation RootedBooleanPhase
open FirstSuccess ResidualMixture FiniteLawMoments
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseTrajectory (historyPrefix initial_prefix_expectation)
open scoped BigOperators Classical

noncomputable section

private lemma event_le_distance {Y : Type*} [Fintype Y] (p q : Y → ℝ)
    (hmass : ∑ y,p y=∑ y,q y) (E : Y → Prop) :
    (∑ y,p y*(if E y then 1 else 0))≤
      (∑ y,q y*(if E y then 1 else 0))+distance p q := by
  have h := distance_event p q hmass (Finset.univ.filter E)
  rw [Finset.sum_filter,Finset.sum_filter] at h
  simp only [mul_ite,mul_one,mul_zero]
  linarith [le_abs_self ((∑ y,if E y then p y else 0)-(∑ y,if E y then q y else 0))]

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Every event of the actual observed Boolean trajectory is bounded by
the source list-path event plus one proved row error per transition. -/
theorem recorded_event_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N : ℕ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (recordedWalk A R C K j k N N hK hW xi v w S bits)) then (1:ℝ) else 0)≤
      (targetChain A R j hp w hw).pathExpectation N S (fun l => if E l then 1 else 0)+
        N*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  let p := pathLaw A R C K j k N N hK hW xi v w S
  let q := targetPathMass A R j hp w hw N N S
  have hq : ∑ b,q b=1 := by
    have hh := initial_prefix_expectation (targetChain A R j hp w hw) N S (fun _ => (1:ℝ))
    simpa only [targetPathMass,q,mul_one,FiniteChain.pathExpectation_const] using hh
  have hpq : (∑ b,(p.mass b:ℝ))=∑ b,q b := by rw [hq]; exact_mod_cast p.total
  have he := event_le_distance (fun b => (p.mass b:ℝ)) q hpq (fun b => E (historyPrefix b))
  have hd := path_distance_bound A R C hC K j k hK hW hB hj xi hx0 hx1 hPL hCheeger v hp w hw N N S
  have hword := word_expectation (recordedWalk A R C K j k N N hK hW xi v w S)
    (fun b => if E (historyPrefix b) then (1:ℝ) else 0)
  rw [recordedWalk_law] at hword
  change _=∑ b,(p.mass b:ℝ)*(if E (historyPrefix b) then 1 else 0) at hword
  have htarget := initial_prefix_expectation (targetChain A R j hp w hw) N S
    (fun l => if E l then (1:ℝ) else 0)
  change (∑ b,q b*(if E (historyPrefix b) then 1 else 0))=_ at htarget
  rw [hword]
  exact he.trans (by rw [htarget]; exact add_le_add_right hd _)

end
end ContingencyTables.RootedPhaseTrajectory

end OAI
