import Mathlib
import OAI.Combinatorics.UniformKServer.PiIntegrate
import OAI.Combinatorics.UniformKServer.TierInner
import OAI.Combinatorics.UniformKServer.TierFrozen

namespace OAI

                                     
section

/-! Actual full-tape one-tier edit estimates. Prefix and suffix may depend
arbitrarily on the tape; the noncoverage ledger is not conditioned on either. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqEdit : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqEdit : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqEdit : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def tierTrigger (D : Data X N H) (n : Fin N) (i : Fin H) : Prop :=
  TierSchedule.trigger D.r (D.K i) (TierSchedule.run D.r (D.K i) (D.qualify i) D.center n.val)
    (D.qualify i) D.center n

def tierEdit (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D) (ω : Tape D) : ℝ :=
  KeyEdits.changed (earlier ω) id (later ω) (D.tierKey ω n.val i p) (D.tierKey ω (n.val+1) i p)

theorem tierEdit_frozen (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (hn : ¬D.tierTrigger n i) (ω : Tape D) :
    D.tierEdit n i p earlier later ω=0 ∧
      D.tierUncovered ω (n.val+1) i p=D.tierUncovered ω n.val i p := by
  have he : D.tierKey ω (n.val+1) i p=D.tierKey ω n.val i p := by
    unfold tierKey
    rw [TierLabeledKeys.frozen D.r (D.K i) (D.qualify i) D.center n hn]
  constructor
  · simp only [tierEdit,he,KeyEdits.changed,ite_true]
  · unfold tierUncovered; rw [he]

theorem tier_expect_bound (D : Data X N H) (i : Fin H) (f : Tape D→ℝ) (c : ℝ)
    (h : ∀ (heavy : HeavyTape D) (b : ∀ j : {j : Fin H // j≠i}, TierTape D j.val)
      (rad : Fin N→TierRadius.Sample (X:=X) (Real.log (1+(D.K i:ℝ)^2)) D.r),
      (TierLifetimes.law (D.K i) (D.quota i)).expect (fun τ=>
        f (heavy,(Equiv.piSplitAt i (TierTape D)).symm ((τ,rad),b)))≤c) :
    D.law.expect f≤c := by
  change ((Law.pi fun _:Fin N=>HeavyRadius.law (X:=X) D.r).prod (Law.pi D.tierLaw)).expect _≤_
  rw [Law.expect_pair]
  apply (le_trans ((Law.pi _).expect_mono _ (fun _=>c) _))
  · exact Law.expect_const _ _ |>.le
  intro heavy
  apply Law.expect_pi_fiber_le D.tierLaw i _ c
  intro b
  change ((TierLifetimes.law (D.K i) (D.quota i)).prod _).expect _≤c
  rw [Law.expect_pair_reverse]
  exact ((Law.pi _).expect_mono _ (fun _=>c) (h heavy b)).trans_eq (Law.expect_const _ _)

theorem tier_stationary (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (γ : ℝ) (hγ : γ≤1/2) (hn : D.tierTrigger n i)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω, (earlier ω).isSome=true) :
    D.law.expect (fun ω=>D.tierEdit n i p earlier later ω+
      D.tierUncovered ω (n.val+1) i p-D.tierUncovered ω n.val i p)≤
      98/(D.K i:ℝ)*(if dist (D.center n) p≤22*D.r ∧ (¬D.heavy n ∨ γ*D.r<dist (D.center n) p) then 1 else 0) := by
  apply tier_expect_bound D i
  intro heavy b rad
  let z := fun τ : TierLifetimes.Tape N =>
    (heavy,(Equiv.piSplitAt i (TierTape D)).symm ((τ,rad),b))
  have hz (τ : TierLifetimes.Tape N) : (z τ).2 i=(τ,rad) := by simp [z,Equiv.piSplitAt]
  have h := TierLabeledKeys.annular_stationary D.r γ D.positive hγ (D.K i) (D.two i)
    (D.quota i) (D.qualify i) D.center n hn rad p (D.heavy n)
    (fun τ=>earlier (z τ)) (fun _ l=>Sum.inr (Sum.inl ⟨i,l⟩)) (fun τ=>later (z τ))
    (fun hh hp τ=>he hh hp (z τ))
  convert h using 1
  apply congrArg (TierLifetimes.law (D.K i) (D.quota i)).expect
  funext τ
  change D.tierEdit n i p earlier later (z τ)+D.tierUncovered (z τ) (n.val+1) i p-
    D.tierUncovered (z τ) n.val i p=_
  simp only [tierEdit,tierUncovered,tierKey,hz,TierLabeledKeys.changed_map,
    TierLabeledKeys.uncovered_map,Function.id_comp]

theorem tier_mover (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (γ : ℝ) (hn : D.tierTrigger n i)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω, (earlier ω).isSome=true) :
    D.law.expect (fun ω=>D.tierEdit n i p earlier later ω-
      D.tierUncovered ω n.val i p)≤
      49/(D.K i:ℝ)*(if dist (D.center n) p≤22*D.r ∧ (¬D.heavy n ∨ γ*D.r<dist (D.center n) p) then 1 else 0) := by
  apply tier_expect_bound D i
  intro heavy b rad
  let z := fun τ : TierLifetimes.Tape N =>
    (heavy,(Equiv.piSplitAt i (TierTape D)).symm ((τ,rad),b))
  have hz (τ : TierLifetimes.Tape N) : (z τ).2 i=(τ,rad) := by simp [z,Equiv.piSplitAt]
  have h := TierLabeledKeys.annular_mover D.r γ D.positive (D.K i) (D.two i)
    (D.quota i) (D.qualify i) D.center n hn rad p (D.heavy n)
    (fun τ=>earlier (z τ)) (fun _ l=>Sum.inr (Sum.inl ⟨i,l⟩)) (fun τ=>later (z τ))
    (fun hh hp τ=>he hh hp (z τ))
  convert h using 1
  apply congrArg (TierLifetimes.law (D.K i) (D.quota i)).expect
  funext τ
  change D.tierEdit n i p earlier later (z τ)-D.tierUncovered (z τ) n.val i p=_
  simp only [tierEdit,tierUncovered,tierKey,hz,TierLabeledKeys.changed_map,
    TierLabeledKeys.uncovered_map,Function.id_comp]

end UniformKServer.LevelMap.Data

end


end

end OAI
