import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OriginalHistoryPrivate
import OAI.Combinatorics.RamseyFive.Streams.DependentPrivateStream
import OAI.Combinatorics.RamseyFive.Streams.MiddleStream
import OAI.Combinatorics.RamseyFive.Marking.AllHistoryWindowLoss

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance hpsBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance hpsTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance hpsIDE : DecidableEq (Slots w n) := Classical.decEq _

abbrev WindowLiftSample (Ω K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (w n steps : ℕ) := Ω×(BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps×
      (Fin w×Bool→Fin n))

def windowTuple (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (a : Ω) : Slots w n→FlagPair K V := fun i=>S.tuple a (slotEmbedding i)

def actualWindowHistory (ctx : Ω→κ) (steps : ℕ) (z : WindowLiftSample Ω K V w n steps) :
    WindowHistory κ K V w n steps := ((ctx z.1,z.2.1),z.2.2)

def historyStream (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ) :
    SelectedStream (Ω:=WindowLiftSample Ω K V w n steps) (β:=FlagPair K V) N (w*(4*n)) admissible :=
  S.augment (fun a=>fiber (historyObservationLaw (first (pair S.law ctx (windowTuple S)))
    (fiber (pair S.law ctx (windowTuple S))) elig steps) (ctx a,windowTuple S a))

omit [Finite K] [FiniteDimensional K V] in
lemma historyStream_law (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ) :
    (historyStream S ctx elig steps).law=originalHistoryLaw S.law ctx (windowTuple S) elig steps := rfl

def historyPrivateStream (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)
    (Γ : WindowHistory κ K V w n steps→Type) [∀h,Fintype (Γ h)]
    (q : ∀h,Law (Γ h)) :
    SelectedStream (Ω:=Σz : WindowLiftSample Ω K V w n steps,Γ (actualWindowHistory ctx steps z))
      (β:=FlagPair K V) N (w*(2*n)) admissible :=
  ((historyStream S ctx elig steps).reindex (middleEmbedding w n)).augmentSigma
    (fun z=>q (actualWindowHistory ctx steps z))

omit [Finite K] [FiniteDimensional K V] in
lemma historyPrivateStream_density (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)
    (Γ : WindowHistory κ K V w n steps→Type) [∀h,Fintype (Γ h)] (q : ∀h,Law (Γ h)) :
    (historyPrivateStream S ctx elig steps Γ q).density=S.density := rfl

omit [Finite K] [FiniteDimensional K V] in
lemma historyPrivateStream_tuple (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)
    (Γ : WindowHistory κ K V w n steps→Type) [∀h,Fintype (Γ h)] (q : ∀h,Law (Γ h))
    (z : Σz : WindowLiftSample Ω K V w n steps,Γ (actualWindowHistory ctx steps z))
    (i : Fin (w*(2*n))) :
    (historyPrivateStream S ctx elig steps Γ q).tuple z i=
      windowTuple S z.1.1 (Sum.inr (finProdFinEquiv.symm i)) := rfl

omit [Finite K] [FiniteDimensional K V] in
lemma historyPrivateStream_mean {Θ : Type} [Fintype Θ]
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)
    (Γ : WindowHistory κ K V w n steps→Type) [∀h,Fintype (Γ h)] (q : ∀h,Law (Γ h))
    (tables : Law Θ)
    (F : (h : WindowHistory κ K V w n steps)→(Slots w n→FlagPair K V)→Γ h→Θ→ℝ) :
    mean (adaptiveLaw (historyPrivateStream S ctx elig steps Γ q).law (fun _=>tables))
      (fun z=>F (actualWindowHistory ctx steps z.1.1) (windowTuple S z.1.1.1) z.1.2 z.2)=
    mean (preRoundLaw (first (pair S.law ctx (windowTuple S))) (fiber (pair S.law ctx (windowTuple S))) elig steps)
      (fun h=>mean (windowPosterior (fiber (pair S.law ctx (windowTuple S))) h)
        (fun x=>mean (q h) (fun v=>mean tables (F h x v)))) := by
  exact originalHistory_private_mean S.law ctx (windowTuple S) elig steps Γ q tables F
end
end SharpRamseyFive.SelectedTuple

end OAI
