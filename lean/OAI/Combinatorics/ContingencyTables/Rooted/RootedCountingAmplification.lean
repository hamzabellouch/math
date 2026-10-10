import OAI.Combinatorics.ContingencyTables.Rooted.RootedCountingSchedule
import OAI.Combinatorics.ContingencyTables.Transport.FiniteMedianConfidence

namespace OAI

/-! # Logarithmic confidence for the actual adaptive counting estimator -/

namespace ContingencyTables.RootedCountingAmplification

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedCountingSchedule
open CompanionTerminalMass (Endpoints tableCount tableCount_ge_one)
open CompanionTerminalApplication (finalPhase)
open CountingPhaseSchedule GridBoundary FiniteMedianConfidence
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def bitCount (A : Instance I J) (s : Settings A) (delta : ℚ) : ℕ :=
  repetitionCount delta * RootedCountingWords.bitCount A s

def estimate (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (s : Settings A) (delta : ℚ) (bits : Fin (bitCount A s delta) → Bool) : ℚ :=
  rationalMedian (List.ofFn (fun i : Fin (repetitionCount delta) =>
    RootedCountingWords.flatEstimate A R s
      (gridWordEquiv (repetitionCount delta) (RootedCountingWords.bitCount A s) bits i)))

/-- The confidence parameter changes only the number of independent
complete runs, never the internal per-oracle failure allowance. -/
theorem success (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (v : Grid (I := Fin (dimension A)) K) (E : Endpoints A)
    (hW' : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (hfinal : H=finalPhase A L ((epsilon/2:ℚ):ℝ))
    (hC : 0 < C) (hB : (K:ℝ)=binWidth A C) (hH : H ≤ rationalHeight A C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (hp : 0 < Fintype.card (Labels A)) :
    1-(delta:ℝ) ≤ uniformAverage (fun bits :
      Fin (bitCount A (settings A C K H L hK hW (epsilon/2) v) delta) → Bool =>
        if (1-(epsilon:ℝ))*tableCount A ≤
            (estimate A R (settings A C K H L hK hW (epsilon/2) v) delta bits:ℝ) ∧
          (estimate A R (settings A C K H L hK hW (epsilon/2) v) delta bits:ℝ) ≤
            (1+(epsilon:ℝ))*tableCount A then (1:ℝ) else 0) := by
  let s := settings A C K H L hK hW (epsilon/2) v
  let f := RootedCountingWords.flatEstimate A R s
  have heh0 : (0:ℚ) < epsilon/2 := by positivity
  have heh1 : epsilon/2 < 1 := by linarith
  have hbase := constant_success A R C K H L hK hW (epsilon/2) heh0 heh1 v E
    hW' hL hfinal hC hB hH hbox hPL hCheeger hp
  have hbase' : 1-(1/256:ℝ) ≤ uniformAverage
      (fun bits : Fin (RootedCountingWords.bitCount A s) → Bool =>
        if (1-((epsilon/2:ℚ):ℝ))*tableCount A ≤ (f bits:ℝ) ∧
          (f bits:ℝ) ≤ (1+((epsilon/2:ℚ):ℝ))*tableCount A then (1:ℝ) else 0) := by
    refine (show 1-(1/256:ℝ) ≤ 255/256 by norm_num).trans (hbase.trans_eq ?_)
    exact CompanionPhaseWords.average_ext_instances _ _ _ _ (fun bits => by split_ifs <;> rfl)
  have hfailure := CompanionPhaseWords.failure_of_success
    (fun bits : Fin (RootedCountingWords.bitCount A s) → Bool =>
      (1-((epsilon/2:ℚ):ℝ))*tableCount A ≤ (f bits:ℝ) ∧
        (f bits:ℝ) ≤ (1+((epsilon/2:ℚ):ℝ))*tableCount A)
    (1/256) (hbase'.trans_eq
      (CompanionPhaseWords.average_ext_instances _ _ _ _ (fun bits => by split_ifs <;> rfl)))
  have hbad : uniformAverage (fun bits : Fin (RootedCountingWords.bitCount A s) → Bool =>
      if (f bits:ℝ) < (1-(epsilon:ℝ)/2)*tableCount A ∨
        (1+(epsilon:ℝ)/2)*tableCount A < (f bits:ℝ) then (1:ℝ) else 0) ≤ 5/16 := by
    have hh : (1/256:ℝ) ≤ 5/16 := by norm_num
    apply le_trans ?_ hh
    simpa only [not_and_or,not_le,Rat.cast_div,Rat.cast_ofNat] using hfailure
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hZ : (0:ℝ) < tableCount A := by linarith [tableCount_ge_one A]
  have hm := median_confidence_real f
    ((1-(epsilon:ℝ))*tableCount A) ((1-(epsilon:ℝ)/2)*tableCount A)
    ((1+(epsilon:ℝ)/2)*tableCount A) ((1+(epsilon:ℝ))*tableCount A)
    (by nlinarith) (by nlinarith) delta hd hbad
  let test := fun words : Fin (repetitionCount delta) →
      (Fin (RootedCountingWords.bitCount A s) → Bool) =>
    if (1-(epsilon:ℝ))*tableCount A ≤
        (rationalMedian (List.ofFn (fun i => f (words i))):ℝ) ∧
      (rationalMedian (List.ofFn (fun i => f (words i))):ℝ) ≤
        (1+(epsilon:ℝ))*tableCount A then (1:ℝ) else 0
  have heq := uniformAverage_equiv
    (gridWordEquiv (repetitionCount delta) (RootedCountingWords.bitCount A s)) test
  have htransport : uniformAverage test = uniformAverage
      (fun bits : Fin (bitCount A s delta) → Bool =>
        if (1-(epsilon:ℝ))*tableCount A ≤ (estimate A R s delta bits:ℝ) ∧
          (estimate A R s delta bits:ℝ) ≤ (1+(epsilon:ℝ))*tableCount A
        then (1:ℝ) else 0) := by
    refine heq.symm.trans (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_)
    intro bits
    rfl
  exact hm.trans_eq htransport

lemma bitCount_eq (A : Instance I J) (s : Settings A) (delta : ℚ) :
    bitCount A s delta=64*(delta.den.bits.length+1)*RootedCountingWords.bitCount A s := rfl

end
end ContingencyTables.RootedCountingAmplification

end OAI
