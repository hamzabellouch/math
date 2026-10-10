import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.WindowDeletionCount

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance allHistBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance allHistIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
local instance allHistTDE (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ]
  {w n steps rem : ℕ} [Nonempty (Fin n)]

abbrev WindowHistory (κ K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (w n steps : ℕ) :=
  (κ×BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps)×
    (Fin w×Bool→Fin n)

def windowPosterior (p : κ→Law (Slots w n→FlagPair K V)) (z : WindowHistory κ K V w n steps) :
    Law (Slots w n→FlagPair K V) := historyPosterior (p z.1.1) z.1.2

theorem allHistory_window_loss
    (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (S : κ→(Fin w×Bool)→Finset (Fin n)) (hrem : 0<rem) (hn : n≤2*rem)
    (hS : ∀a,0<μ a→∀b,rem+steps≤(S a b).card)
    (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (J d ε s k B : ℝ) (hB : 0≤B)
    (c : κ→BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps→
      Slots w n→Slots w n→ℝ)
    (drop : WindowHistory κ K V w n steps→Fin w→ℝ)
    (E : WindowHistory κ K V w n steps→Finset (Fin w))
    (W : ∀z,∀hE : (E z).Nonempty,
      ReciprocalWindows (windowPosterior p z) (u z) z.2 (survivingOriginal (E z) hE) s)
    (hE : ∀z,0<preRoundLaw μ p S steps z→
      E z=survivingWindowSet (preRoundBad μ p S steps J d ε c z) z.2 (drop z) k)
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (c₀ δ τ P : ℝ) (hδ : 0<δ)
    (hh : ∀z,0<preRoundLaw μ p S steps z→∀v∈E z,∀t,
      preRoundBad μ p S steps J d ε c z (middleSlot v t)=0→
      allWindowFailure f r (windowPosterior p z) (u z) z.2 (E z) (W z)
        σ hσ hq hd c₀ δ τ P hδ v t≤B) :
    mean (preRoundLaw μ p S steps) (fun h=>
      mean (allWindowExperiment f r (windowPosterior p h) (u h) h.2 (E h) (W h)) (fun z=>
        ((allWindowPositions f r (windowPosterior p h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c₀ δ τ P hδ (preRoundBad μ p S steps J d ε c h)
          z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
      5*mean (preRoundLaw μ p S steps) (fun h=>
        ∑i∈blockActive (historyUnused (S h.1.1) h.1.2),preRoundBad μ p S steps J d ε c h i)+
      (2*n:ℝ)*mean (preRoundLaw μ p S steps) (fun h=>
        ((goodWindowSet (preRoundBad μ p S steps J d ε c h) h.2).filter fun v=>k<drop h v).card)+
      (w*(2*n):ℝ)*B := by
  have hb:=mean_mono_pos (preRoundLaw μ p S steps) (fun h hh'=>
    allWindow_loss f r (windowPosterior p h) (u h) h.2 (E h) (W h)
      σ hσ hq hd c₀ δ τ P hδ (preRoundBad μ p S steps J d ε c h) (drop h) k B
      (hE h hh') hB (hh h hh'))
  simp only [mean_add,mean_smul,mean_const] at hb
  have hrdy:=preRound_ready_loss μ p S hrem hn hS J d ε c
  exact hb.trans (add_le_add (add_le_add hrdy le_rfl) le_rfl)
end
end SharpRamseyFive.Marking

end OAI
