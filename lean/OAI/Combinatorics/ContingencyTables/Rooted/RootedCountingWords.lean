import OAI.Combinatorics.ContingencyTables.Rooted.RootedHistoryConfidence

namespace OAI

/-! # Actual adaptive finite-word counting output and its accuracy -/

namespace ContingencyTables.RootedCountingWords

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedStoredHistory RootedHistoryStep
open RootedHistoryConfidence
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def estimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : Fin s.H → Word A s) : ℚ :=
  (lookup A (decoded A R s (List.ofFn words)) s.H).estimate

lemma estimate_accurate (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (s : Settings A) (E : Endpoints A) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^s.L)
    (hfinal : s.H=finalPhase A s.L epsilon) (eta : ℝ)
    (herr : (s.H:ℝ)*(4*(s.xi:ℝ)+4*eta) ≤ epsilon/50)
    (words : Fin s.H → Word A s) (hg : GoodWords A R s eta (List.ofFn words)) :
    (1-epsilon)*tableCount A ≤ (estimate A R s words:ℝ) ∧
      (estimate A R s words:ℝ) ≤ (1+epsilon)*tableCount A := by
  have hlen : (decoded A R s (List.ofFn words)).length=s.H := by
    rw [decoded_length,List.length_ofFn]
  have h := count_accuracy A R E s.L epsilon he0 he1 hW hL s.xi eta
    (by simpa only [hfinal] using herr) (decoded A R s (List.ofFn words))
    (hlen.trans hfinal) hg
  simpa only [hlen,estimate] using h

/-- The actual stored rational value has the stated error probability.
No equality to an ideal empirical-ratio estimator is assumed. -/
theorem accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (E : Endpoints A) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^s.L)
    (hfinal : s.H=finalPhase A s.L epsilon)
    (hC : 0 < s.C) (hB : (s.K:ℝ)=binWidth A s.C)
    (hH : s.H ≤ rationalHeight A s.C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^s.L)
    (hx0 : 0 < s.xi) (hx1 : s.xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) s.K))
    (hp : 0 < Fintype.card (Labels A)) (hn : 0 < s.n)
    (eta : ℝ) (he0' : 0 < eta) (he1' : eta ≤ 1/4)
    (herr : (s.H:ℝ)*(4*(s.xi:ℝ)+4*eta) ≤ epsilon/50) :
    1-(s.H:ℝ)*error A s eta s.H ≤
      uniformAverage (fun words : Fin s.H → Word A s =>
        if (1-epsilon)*tableCount A ≤ (estimate A R s words:ℝ) ∧
          (estimate A R s words:ℝ) ≤ (1+epsilon)*tableCount A then (1:ℝ) else 0) := by
  have hg := history_success A R s hC hB hH hbox hx0 hx1 hPL hCheeger hp hn eta he0' he1'
  apply hg.trans
  apply uniformAverage_mono
  intro words
  by_cases h : GoodWords A R s eta (List.ofFn words)
  · have ha := estimate_accurate A R s E epsilon he0 he1 hW hL hfinal eta herr words h
    simp [h,ha]
  · simp only [h,ite_false]
    split_ifs <;> norm_num

def bitCount (A : Instance I J) (s : Settings A) : ℕ := s.H*totalWidth A s

def flatEstimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (bits : Fin (bitCount A s) → Bool) : ℚ :=
  estimate A R s (gridWordEquiv s.H (totalWidth A s) bits)

lemma flatEstimate_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (P : ℚ → Prop) :
    uniformAverage (fun bits : Fin (bitCount A s) → Bool =>
      if P (flatEstimate A R s bits) then (1:ℝ) else 0)=
      uniformAverage (fun words : Fin s.H → Word A s =>
        if P (estimate A R s words) then (1:ℝ) else 0) := by
  have he := uniformAverage_equiv (gridWordEquiv s.H (totalWidth A s))
    (fun words : Fin s.H → Word A s =>
      if P (estimate A R s words) then (1:ℝ) else 0)
  refine (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_).trans
    (he.trans (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_))
  · intro bits
    rfl
  · intro words
    rfl

end
end ContingencyTables.RootedCountingWords

end OAI
