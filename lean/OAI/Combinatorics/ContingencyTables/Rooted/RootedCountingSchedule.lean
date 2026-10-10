import OAI.Combinatorics.ContingencyTables.Rooted.RootedCountingWords
import OAI.Combinatorics.ContingencyTables.Counting.CountingPhaseSchedule

namespace OAI

/-! # An explicit constant-confidence schedule for the actual counting words -/

namespace ContingencyTables.RootedCountingSchedule

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedHistoryStep
open CompanionTargetMixing (restartTime)
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open CountingPhaseSchedule GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

/-- Only natural/rational arithmetic selects the phase precision and
all finite loops. The supplied grid point is the evaluator's fixed start. -/
def settings (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ)
    (v : Grid (I := Fin (dimension A)) K) : Settings A :=
  let p := Fintype.card (Labels A)
  let tau := restartTime A H L
  let eta := tolerance H epsilon
  let N := observations p A.W H eta
  let n := returnCap p H tau
  let k := precision H tau N n eta
  ⟨C,K,H,L,k,n,N,initialPrecision H,hK,hW,noise H tau N n eta,v⟩

lemma settings_positive (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K) :
    0 < (settings A C K H L hK hW epsilon v).xi ∧
      (settings A C K H L hK hW epsilon v).xi ≤ 1/4 ∧
      0 < (settings A C K H L hK hW epsilon v).n := by
  dsimp only [settings]
  refine ⟨noise_pos _ _ _ _ _,?_,returnCap_pos _ _ _⟩
  exact (noise_le_tolerance _ _ _ _ _ (tolerance_pos H epsilon he0)).trans
    (tolerance_le_quarter H epsilon he0 he1)

lemma observable_cast (p W : ℕ) :
    (observable p W:ℝ)=ObservableBounds.observableConstant (p:ℝ) ((W:ℝ)^2) := by
  simp only [observable,ObservableBounds.observableConstant,Nat.cast_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  ring

lemma error_bound (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ) (he : 0 < epsilon)
    (v : Grid (I := Fin (dimension A)) K) :
    error A (settings A C K H L hK hW epsilon v) (tolerance H epsilon:ℝ) H ≤
      1/(256*((H:ℝ)+1)) := by
  let p := Fintype.card (Labels A)
  let tau := restartTime A H L
  let eta := tolerance H epsilon
  let N := observations p A.W H eta
  let n := returnCap p H tau
  let k := precision H tau N n eta
  let xi := noise H tau N n eta
  have he : 0 < eta := tolerance_pos H epsilon he
  have hc : (observationCoefficient p A.W:ℝ)=32000*(p:ℝ)^8*
      ObservableBounds.observableConstant p ((A.W:ℝ)^2) := by
    simp only [observationCoefficient,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,
      observable_cast]
  have hb := combine_error p H tau N n k (initialPrecision H)
    (observationCoefficient p A.W) eta xi (1/(1024*((H:ℝ)+1)))
    (by exact_mod_cast (noise_pos H tau N n eta).le)
    (precision_error H tau N n eta)
    (observations_error p A.W H eta he)
    (initial_error H)
    (cap_error p H tau)
    (noise_error H tau N n eta)
  have hfour : (4:ℝ)*(1/(1024*((H:ℝ)+1)))=1/(256*((H:ℝ)+1)) := by
    field_simp
    ring
  rw [hfour] at hb
  simpa only [error,settings,hc,p,tau,eta,N,n,k,xi] using hb

lemma total_error_bound (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ) (he : 0 < epsilon)
    (v : Grid (I := Fin (dimension A)) K) :
    (H:ℝ)*error A (settings A C K H L hK hW epsilon v)
      (tolerance H epsilon:ℝ) H ≤ 1/256 := by
  have hb := mul_le_mul_of_nonneg_left (error_bound A C K H L hK hW epsilon he v)
    (Nat.cast_nonneg H : (0:ℝ) ≤ H)
  refine hb.trans ?_
  rw [mul_one_div,div_le_iff₀ (by positivity : (0:ℝ) < 256*((H:ℝ)+1))]
  linarith

lemma logarithmic_bound (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ) (he : 0 < epsilon)
    (v : Grid (I := Fin (dimension A)) K) :
    (H:ℝ)*(4*((settings A C K H L hK hW epsilon v).xi:ℝ)+
      4*(tolerance H epsilon:ℝ)) ≤ (epsilon:ℝ)/50 :=
  logarithmic_error H (restartTime A H L)
    (observations (Fintype.card (Labels A)) A.W H (tolerance H epsilon))
    (returnCap (Fintype.card (Labels A)) H (restartTime A H L)) epsilon he

/-- Constant success for the actual finite Boolean estimator. The
binary confidence parameter is handled by independent medians afterward. -/
theorem constant_success (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (epsilon : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K) (E : Endpoints A)
    (hW' : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (hfinal : H=finalPhase A L (epsilon:ℝ))
    (hC : 0 < C) (hB : (K:ℝ)=binWidth A C) (hH : H ≤ rationalHeight A C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (hp : 0 < Fintype.card (Labels A)) :
    255/256 ≤ uniformAverage (fun bits :
      Fin (RootedCountingWords.bitCount A (settings A C K H L hK hW epsilon v)) → Bool =>
        if (1-(epsilon:ℝ))*tableCount A ≤
            (RootedCountingWords.flatEstimate A R (settings A C K H L hK hW epsilon v) bits:ℝ) ∧
          (RootedCountingWords.flatEstimate A R (settings A C K H L hK hW epsilon v) bits:ℝ) ≤
            (1+(epsilon:ℝ))*tableCount A then (1:ℝ) else 0) := by
  let s := settings A C K H L hK hW epsilon v
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have heR1 : (epsilon:ℝ) < 1 := by exact_mod_cast he1
  have hs := settings_positive A C K H L hK hW epsilon he0 he1 v
  have htR : (tolerance H epsilon:ℝ) ≤ 1/4 := by
    have ht := tolerance_le_quarter H epsilon he0 he1
    have ht' : (tolerance H epsilon:ℝ) ≤ ((1/4:ℚ):ℝ) := Rat.cast_le.mpr ht
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at ht'
    exact ht'
  have hprob := RootedCountingWords.accuracy A R s E epsilon heR heR1 hW' hL hfinal
    hC hB hH hbox hs.1 hs.2.1 hPL hCheeger hp hs.2.2
    (tolerance H epsilon) (by exact_mod_cast tolerance_pos H epsilon he0)
    htR
    (logarithmic_bound A C K H L hK hW epsilon he0 v)
  have hb := total_error_bound A C K H L hK hW epsilon he0 v
  have hlaw := RootedCountingWords.flatEstimate_law A R s (fun estimate =>
    (1-(epsilon:ℝ))*tableCount A ≤ (estimate:ℝ) ∧
      (estimate:ℝ) ≤ (1+(epsilon:ℝ))*tableCount A)
  apply ((show (255/256:ℝ) ≤ 1-(H:ℝ)*error A s (tolerance H epsilon:ℝ) H by
    linarith).trans hprob).trans_eq
  refine (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_).trans
    (hlaw.symm.trans (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_))
  · intro words
    split_ifs <;> rfl
  · intro bits
    split_ifs <;> rfl

end
end ContingencyTables.RootedCountingSchedule

end OAI
