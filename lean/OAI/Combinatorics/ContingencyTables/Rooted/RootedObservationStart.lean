import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseExperiment

namespace OAI

/-! # Actual phase observations from an approximate warm start -/

namespace ContingencyTables.RootedObservationStart

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity RootedAnnealing RootedMultiplierUpdate
open RootedPhaseExperiment RootedPhaseWords RootedPhaseAccuracy
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseWords (phaseBits Stored)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma bounded_expectation_error {X : Type*} [Fintype X]
    (p q g : X → ℝ) (hg : ∀ x,0 ≤ g x ∧ g x ≤ 1) :
    (∑ x,p x*g x) ≤ (∑ x,q x*g x)+2*distance p q := by
  have hp (x : X) : p x*g x ≤ q x*g x+|p x-q x| := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (p x-q x)) (hg x).1
    have h2 := mul_le_mul_of_nonneg_left (hg x).2 (abs_nonneg (p x-q x))
    nlinarith
  have h := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => hp x)
  simp only [Finset.sum_add_distrib] at h
  unfold distance
  linarith

variable {I J : Type} [Fintype I] [Fintype J]

theorem observed_failure_near (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0 < w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (p q : State A → ℝ) (hq : ∀ S,0 ≤ q S) (hmass : ∑ S,q S ≤ 1)
    (hwarm : ∀ S,q S ≤ (10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (eta : ℝ) (heta : 0 < eta) :
    (∑ S,p S*uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits))))) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+2*distance p q := by
  let g : State A → ℝ := fun S =>
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits))))
  have hg (S : State A) : 0 ≤ g S ∧ g S ≤ 1 := by
    apply FiniteIndependentAverages.mean_bounds _ 0 1
    intro bits
    unfold eventIndicator
    split_ifs <;> norm_num
  have he := bounded_expectation_error p q g hg
  have hs := observed_failure A R C hC K j k N hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw hgood q hq hmass hwarm eta heta
  dsimp only [g] at he
  have hsadd := _root_.add_le_add hs (le_refl (2*distance p q))
  have hb := he.trans hsadd
  exact hb

end
end ContingencyTables.RootedObservationStart

end OAI
