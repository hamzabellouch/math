import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.WindowStage
import OAI.Combinatorics.RamseyFive.Geometry.StreamGeometry

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree MessageWeights ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance cwsBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance cwsTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance cwsIDE : DecidableEq (Slots w n) := Classical.decEq _
variable (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
  (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)
  (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
  (E : WindowHistory κ K V w n steps→Finset (Fin w)) {s : ℝ}
  (W : ∀h,∀he : (E h).Nonempty,ReciprocalWindows (windowPosterior (windowFiber S ctx) h)
    (u h) h.2 (survivingOriginal (E h) he) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)
omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma levelWindowStream_geometric {M : ℝ} (hG : Geometric S M) :
    Geometric (levelWindowStream S ctx elig steps u E W) M := by
  exact ((hG.augment _).reindex (middleEmbedding w n)).augmentSigma _
theorem actualWindow_coded {l : ℕ} (hl : l<w*(2*n))
    (bad : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (L J M : ℝ) (hG : Geometric S M) (hf : ∀C,(f C).Normalized) (hr : ∀C,(r C).Normalized)
    (hcost : ∀h,∀v : WindowLevelsData (K:=K) (V:=V) (E h).card,∀t,
      variableTreeCost f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c δ τ P hδ t v)≤L)
    (hcap : ∀h,∀v : WindowLevelsData (K:=K) (V:=V) (E h).card,∀t j,
      Real.log (variableTreeDomain f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c δ τ P hδ t v) j).card≤J)
    (hloss : mean (preRoundLaw (first (pair S.law ctx (windowTuple S))) (windowFiber S ctx) elig steps)
      (fun h=>mean (allWindowExperiment f r (windowPosterior (windowFiber S ctx) h)
        (u h) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
            σ hσ hq hd c δ τ P hδ (bad h) z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
      ((w*(2*n):ℝ)-l)/10) :
    Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
      (L+(w+1)*Real.log (l+1)) J M) := by
  obtain ⟨t,hE,hden,⟨C⟩⟩:=actualWindow_stage S ctx elig steps f r u E W σ hσ hq hd c δ τ P hδ
    hl bad L J hf hr hcost hcap hloss
  refine ⟨{ sample:=_ ,stream:=_ ,code:=_ ,description:=C,density_bound:=hden,geometric:=?_ }⟩
  exact ((levelWindowStream_geometric S ctx elig steps u E W hG).restrict _ hE).extract hl.le _
end
end SharpRamseyFive.SelectedTuple

end OAI
