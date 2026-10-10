import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.HistoryPrivateStream
import OAI.Combinatorics.RamseyFive.Entropy.ContextDescription
import OAI.Combinatorics.RamseyFive.Decoding.FinsetEquivPositions

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree MessageWeights ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance awsBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance awsTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance awsIDE : DecidableEq (Slots w n) := Classical.decEq _
variable (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
  (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)

abbrev windowFiber := fiber (pair S.law ctx (windowTuple S))

def levelWindowStream (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (E : WindowHistory κ K V w n steps→Finset (Fin w)) {s : ℝ}
    (W : ∀h,∀he : (E h).Nonempty,ReciprocalWindows (windowPosterior (windowFiber S ctx) h)
      (u h) h.2 (survivingOriginal (E h) he) s) :=
  historyPrivateStream S ctx elig steps
    (fun h=>WindowLevelsData (K:=K) (V:=V) (E h).card)
    (fun h=>allWindowLevelLaw (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h))

variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
  (E : WindowHistory κ K V w n steps→Finset (Fin w)) {s : ℝ}
  (W : ∀h,∀he : (E h).Nonempty,ReciprocalWindows (windowPosterior (windowFiber S ctx) h)
    (u h) h.2 (survivingOriginal (E h) he) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

abbrev LevelWindowSample := (z : WindowLiftSample Ω K V w n steps)×
  WindowLevelsData (K:=K) (V:=V) (E (actualWindowHistory ctx steps z)).card

def actualWindowEncoded (t : VariableTreeTape f r w) (z : LevelWindowSample ctx steps E) :=
  let h:=actualWindowHistory ctx steps z.1
  allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
    σ hσ hq hd c δ τ P hδ t z.2

def actualWindowPositions (bad : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (t : VariableTreeTape f r w) (z : LevelWindowSample ctx steps E) : Finset (Fin (w*(2*n))) :=
  let h:=actualWindowHistory ctx steps z.1
  equivPositions finProdFinEquiv
    (allWindowPositions f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
      σ hσ hq hd c δ τ P hδ (bad h) t (windowTuple S z.1.1,z.2))

lemma actualWindow_loss_mean (bad : WindowHistory κ K V w n steps→Slots w n→ℝ) :
    mean (adaptiveLaw (levelWindowStream S ctx elig steps u E W).law (fun _=>variableTreeLaw f r w))
      (fun z=>((actualWindowPositions S ctx steps f r u E W σ hσ hq hd c δ τ P hδ bad z.2 z.1)ᶜ.card:ℝ))=
    mean (preRoundLaw (first (pair S.law ctx (windowTuple S))) (windowFiber S ctx) elig steps)
      (fun h=>mean (allWindowExperiment f r (windowPosterior (windowFiber S ctx) h)
        (u h) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
            σ hσ hq hd c δ τ P hδ (bad h) z.2.2 (z.1,z.2.1))ᶜ.card:ℝ))) := by
  unfold actualWindowPositions
  simp only [equivPositions_compl_card]
  have h:=historyPrivateStream_mean S ctx elig steps
    (fun h=>WindowLevelsData (K:=K) (V:=V) (E h).card)
    (fun h=>allWindowLevelLaw (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h))
    (variableTreeLaw f r w)
    (fun h x v t=>((allWindowPositions f r (windowPosterior (windowFiber S ctx) h)
      (u h) h.2 (E h) (W h) σ hσ hq hd c δ τ P hδ (bad h) t (x,v))ᶜ.card:ℝ))
  simpa only [levelWindowStream,allWindowExperiment,mean_adaptive] using h

theorem actualWindow_stage {l : ℕ} (hl : l<w*(2*n))
    (bad : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (L M : ℝ) (hf : ∀C,(f C).Normalized) (hr : ∀C,(r C).Normalized)
    (hcost : ∀h,∀v : WindowLevelsData (K:=K) (V:=V) (E h).card,∀t,
      variableTreeCost f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c δ τ P hδ t v)≤L)
    (hcap : ∀h,∀v : WindowLevelsData (K:=K) (V:=V) (E h).card,∀t j,
      Real.log (variableTreeDomain f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c δ τ P hδ t v) j).card≤M)
    (hloss : mean (preRoundLaw (first (pair S.law ctx (windowTuple S))) (windowFiber S ctx) elig steps)
      (fun h=>mean (allWindowExperiment f r (windowPosterior (windowFiber S ctx) h)
        (u h) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
            σ hσ hq hd c δ τ P hδ (bad h) z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
      ((w*(2*n):ℝ)-l)/10) :
    ∃ (t : VariableTreeTape f r w)
      (hE : 0<eventMass (levelWindowStream S ctx elig steps u E W).law
        (Finset.univ.filter fun z=>l≤(actualWindowPositions S ctx steps f r u E W
          σ hσ hq hd c δ τ P hδ bad t z).card)),
      let S':=((levelWindowStream S ctx elig steps u E W).restrict _ hE).extract hl.le
        (actualWindowPositions S ctx steps f r u E W σ hσ hq hd c δ τ P hδ bad t)
      S'.density≤(10/9)*S.density ∧
      Nonempty (ContextDescription
        (κ:=VariableTreeMessage f r t (Finset.univ,Finset.univ)×RunAssignment l (w+1))
        S'.law S'.tuple (L+(w+1)*Real.log (l+1)) M) := by
  obtain ⟨t,hE,_,hden,hdesc⟩:=fixed_table_stage_dependent hl
    (levelWindowStream S ctx elig steps u E W) (variableTreeLaw f r w)
    (fun t=>VariableTreeMessage f r t (Finset.univ,Finset.univ))
    (actualWindowPositions S ctx steps f r u E W σ hσ hq hd c δ τ P hδ bad)
    (actualWindowEncoded S ctx steps f r u E W σ hσ hq hd c δ τ P hδ)
    (fun t=>variableTreeDomain f r t (Finset.univ,Finset.univ))
    (fun z i=>survivorRank (E (actualWindowHistory ctx steps z.1))
      (finProdFinEquiv.symm i : Fin w×Fin (2*n)).1)
    (fun _=>middleRank_monotone _)
    (fun t=>variableTreeCost f r t (Finset.univ,Finset.univ)) L M
    (fun t=>variableTree_weight f r t _ hf hr)
    (fun t z _=>hcost _ z.2 t) (fun t z _ j=>hcap _ z.2 t j) (by
      intro t z _ i hi
      rw [actualWindowPositions,mem_equivPositions] at hi
      exact (Finset.mem_filter.mp hi).2.2.2) (by
      convert (actualWindow_loss_mean S ctx elig steps f r u E W σ hσ hq hd c δ τ P hδ bad).trans_le hloss using 1
      · apply congrArg (mean _)
        funext z
        congr 2
        ext i
        simp only [Finset.mem_compl]
      · simp only [Nat.cast_mul,Nat.cast_ofNat])
  refine ⟨t,hE,hden,?_⟩
  simpa only [Nat.cast_add,Nat.cast_one] using hdesc
end
end SharpRamseyFive.SelectedTuple

end OAI
