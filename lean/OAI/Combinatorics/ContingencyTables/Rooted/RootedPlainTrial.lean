import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseTrial
import OAI.Combinatorics.ContingencyTables.Machines.FinitePlainLift

namespace OAI

/-! # A selected-root phase begun from its actual transversal law -/

namespace ContingencyTables.RootedPlainTrial

open CommonBasesFPRAS FirstSuccess ResidualMixture RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open RootedAnnealing RootedWarmStart RootedPhaseTrial
open CompanionPhaseWords (Stored)
open CompanionConcentration (pairs_ne_nil)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma lift_warm (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0 < Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (q : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hq : ∀ S,q S ≤ 2*law A R j S.val.val)
    (S : ChainIndex (pairs : List (Pair A))) :
    plainLift pairs q S ≤ (10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j) := by
  have hpos : ∀ p q,0 < (w p q:ℝ) := fun p q => by exact_mod_cast hw p q
  have htrace (T : PlainIndex (pairs : List (Pair A))) :
      q T ≤ 2*(metropolisTrace pairs PairedLabels.fresh (pairs_ne_nil A hp)
        PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j) hpos
        (weight_positive A R j)).π T := by
    rw [metropolisTrace_pi]
    exact hq T
  have h := plainLift_warm pairs PairedLabels.fresh (pairs_ne_nil A hp)
    PairedLabels.cover (fun p q => (w p q:ℝ)) (weight A R j)
    (weight_positive A R j) hgood q htrace S
  simpa only [PairedLabels.length] using h

/-- The incoming law is the actual rational output law on transversals;
only the comparison reference is warm. -/
theorem trial_failure (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (old : Stored A) (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (old.multiplier p q:ℝ)))
    (p : RationalLaw (PlainIndex (pairs : List (Pair A))))
    (q : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hq : ∀ S,0 ≤ q S) (hq1 : ∑ S,q S ≤ 1)
    (hwarm : ∀ S,q S ≤ 2*law A R j S.val.val)
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    (∑ S,(p.mass S:ℝ)*uniformAverage (fun bits : TrialWords A C K j k N xi =>
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S.val bits=some next ∧
        ValidOutput A R j old xi eta next))) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+
          2*distance (fun S => (p.mass S:ℝ)) q+2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
  have hp0 (S : PlainIndex (pairs : List (Pair A))) : 0 ≤ (p.mass S:ℝ) := by
    exact_mod_cast p.nonnegative S
  have hp1 : (∑ S,(p.mass S:ℝ))=1 := by exact_mod_cast p.total
  have hfull := RootedPhaseTrial.trial_failure A R C hC K j k N hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp old hw hE hgood
    (plainLift pairs (fun S => (p.mass S:ℝ))) (plainLift pairs q)
    (plainLift_nonneg pairs _ hp0)
    (by rw [plainLift_mass]; exact hp1)
    (plainLift_nonneg pairs _ hq)
    (by rw [plainLift_mass]; exact hq1)
    (lift_warm A R j hp old.multiplier hw hgood q hwarm) eta he0 he1
  rw [FinitePlainLift.sum_mul,FinitePlainLift.distance_lift] at hfull
  exact hfull

end
end ContingencyTables.RootedPlainTrial

end OAI
