import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Decoding.CutProjectionGeometry
import OAI.Computability.PerfectCompleteness.Foundations.OriginalTerminalSplitLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayGroupingTransport

namespace OAI

section

namespace PerfectCompleteness.CutGroupedProjection

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls
open scoped BigOperators Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def cutProjection (p : Path branch n (m + 1))
    {left right : Slots branch n → Fin t → MixedSupport.Slot}
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) :
    ∀ s k, MixedSupport.Projection
      (WholeCutGrouping.cutSlots p left s k) (WholeCutGrouping.cutSlots p right s k) :=
  fun s k => q (p.slotEmbedding s) k

def terminalPullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    {left right : Slots branch n → Fin t → MixedSupport.Slot}
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (terminal : CutTerminalSplit.TerminalTape F2 repeats p (LeafDomain right)) :
    CutTerminalSplit.TerminalTape F2 repeats p (LeafDomain left) :=
  fun call child => ChildBlockProjection.squarePullback
    (ChildAssemblyProjection.childProjection (cutProjection p q) child) (terminal call child)

def factorPullback (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (left right : Slots branch n → Fin t → MixedSupport.Slot) →
      (∀ s k, MixedSupport.Projection (left s k) (right s k)) →
      (j : DrawIndex repeats p) →
      CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain right) j →
        CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain left) j
  | _ + 1, _, .refl _, _, _, q, _, x =>
      fun child => ChildBlockProjection.squarePullback
        (ChildAssemblyProjection.childProjection q child) (x child)
  | _ + 1, _, .step i p, left, right, q, j, x =>
      match j with
      | Sum.inl j =>
          ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection q j.val) x
      | Sum.inr j =>
          factorPullback repeats p (childSlots left i) (childSlots right i)
            (ChildAssemblyProjection.childProjection q i) j.2 x

def tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (tape : CutSamplerRefinement.Tape F2 repeats p (LeafDomain right)) :
    CutSamplerRefinement.Tape F2 repeats p (LeafDomain left) :=
  fun j => factorPullback repeats p left right q j (tape j)

theorem evaluate_tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (tape : CutSamplerRefinement.Tape F2 repeats p (LeafDomain right)) (x : Domain left),
      (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain left)
        (tapePullback repeats p left right q tape)).val x =
      (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain right) tape).val
        (sourceProjection q x) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q tape x
          exact congrArg (fun f : H left => f.val x)
            (ChildAssemblyProjection.recursiveSum_pullback q (tape ()))
      | step i p =>
          intro left right q tape x
          simp only [CutSamplerLocality.evaluate_step, RecursiveSampler.combine,
            RecursiveSampler.combineFunction, Finset.sum_apply, Pi.add_apply, Pi.mul_apply,
            PointwiseSpaces.pullback_apply]
          change
            (∑ j : OffPath i,
              (ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection q j.val)
                (tape (.inl j))).val (restrictChild left j.val x)) +
              (∑ h : Fin (repeats (n + 1)),
                (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain (childSlots left i))
                  (tapePullback repeats p (childSlots left i) (childSlots right i)
                    (ChildAssemblyProjection.childProjection q i)
                    (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h false))).val
                      (restrictChild left i x) *
                (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain (childSlots left i))
                  (tapePullback repeats p (childSlots left i) (childSlots right i)
                    (ChildAssemblyProjection.childProjection q i)
                    (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h true))).val
                      (restrictChild left i x)) =
            (∑ j : OffPath i, (tape (.inl j)).val (restrictChild right j.val (sourceProjection q x))) +
              (∑ h : Fin (repeats (n + 1)),
                (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain (childSlots right i))
                  (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h false)).val
                    (restrictChild right i (sourceProjection q x)) *
                (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain (childSlots right i))
                  (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h true)).val
                    (restrictChild right i (sourceProjection q x)))
          apply congrArg₂ (fun a b : F2 => a + b)
          · exact Finset.sum_congr rfl (fun _ _ => rfl)
          · apply Finset.sum_congr rfl
            intro h _
            apply congrArg₂ (fun a b : F2 => a * b)
            · exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h false)
                (restrictChild left i x)
            · exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h true)
                (restrictChild left i x)

theorem terminalFactor_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (call : TerminalIndex repeats p)
      (x : CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain right)
        (drawIndex repeats p call)),
      CutTerminalSplit.terminalFactorEquiv F2 repeats p (LeafDomain left) call
          (factorPullback repeats p left right q (drawIndex repeats p call) x) =
        fun child => ChildBlockProjection.squarePullback
          (ChildAssemblyProjection.childProjection (cutProjection p q) child)
          (CutTerminalSplit.terminalFactorEquiv F2 repeats p (LeafDomain right) call x child) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q call x
          cases call
          rfl
      | step i p =>
          intro left right q call x
          exact ih p (childSlots left i) (childSlots right i)
            (ChildAssemblyProjection.childProjection q i) call.2 x

theorem exteriorFactor_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
      (_hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k)))
      (j : DrawIndex repeats p) (hj : ¬ IsTerminal repeats p j)
      (x : CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain right) j),
      factorPullback repeats p left right q j x =
        cast (WholeCutExteriorTransport.factor_eq repeats p right left
          (fun s h => (hs s h).symm) j hj) x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q hs hk j hj x
          exact False.elim (hj True.intro)
      | step i p =>
          intro left right q hs hk j hj x
          cases j with
          | inl j =>
              exact CutProjectionGeometry.squarePullback_eq_cast
                (childSlots left j.val) (childSlots right j.val)
                (ChildAssemblyProjection.childProjection q j.val)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs j)
                (fun s k => hk (j.val, s) (WholeCutExteriorTransport.outside_ordinary i p j s) k) x
          | inr j =>
              exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
                (fun s h k => hk (i, s) (WholeCutExteriorTransport.outside_selected i p s h) k)
                j.2 hj x

theorem splitTape_tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (tape : CutSamplerRefinement.Tape F2 repeats p (LeafDomain right)) :
    CutTerminalSplit.splitTape F2 repeats p (LeafDomain left)
        (tapePullback repeats p left right q tape) =
      (terminalPullback repeats p q (CutTerminalSplit.splitTape F2 repeats p (LeafDomain right) tape).1,
        cast (WholeCutExteriorTransport.scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm))
          (CutTerminalSplit.splitTape F2 repeats p (LeafDomain right) tape).2) := by
  apply Prod.ext
  · funext call
    exact terminalFactor_pullback repeats p left right q call (tape (drawIndex repeats p call))
  · funext j
    exact (exteriorFactor_pullback repeats p left right q hs hk j.val j.property (tape j.val)).trans
      (CutSamplerReplayGroupingTransport.cast_pi_apply
        (WholeCutExteriorTransport.scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm))
        (fun j => WholeCutExteriorTransport.factor_eq repeats p right left
          (fun s h => (hs s h).symm) j.val j.property)
        (CutTerminalSplit.splitTape F2 repeats p (LeafDomain right) tape).2 j).symm

theorem evaluate_rebuild (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (terminal : CutTerminalSplit.TerminalTape F2 repeats p (LeafDomain right))
    (exterior : CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain right)) (x : Domain left) :
    (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain left)
      ((CutTerminalSplit.splitTape F2 repeats p (LeafDomain left)).symm
        (terminalPullback repeats p q terminal,
          cast (WholeCutExteriorTransport.scalarExterior_eq repeats p right left
            (fun s h => (hs s h).symm)) exterior))).val x =
    (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain right)
      ((CutTerminalSplit.splitTape F2 repeats p (LeafDomain right)).symm (terminal, exterior))).val
        (sourceProjection q x) := by
  let tape := (CutTerminalSplit.splitTape F2 repeats p (LeafDomain right)).symm (terminal, exterior)
  have hsplit :
      CutTerminalSplit.splitTape F2 repeats p (LeafDomain left)
          (tapePullback repeats p left right q tape) =
        (terminalPullback repeats p q terminal,
          cast (WholeCutExteriorTransport.scalarExterior_eq repeats p right left
            (fun s h => (hs s h).symm)) exterior) := by
    simpa only [tape, Equiv.apply_symm_apply] using
      splitTape_tapePullback repeats p left right q hs hk tape
  have hleft := congrArg (CutTerminalSplit.splitTape F2 repeats p (LeafDomain left)).symm hsplit
  simp only [Equiv.symm_apply_apply] at hleft
  rw [← hleft]
  exact evaluate_tapePullback repeats p left right q tape x

end
end PerfectCompleteness.CutGroupedProjection

end

section

namespace PerfectCompleteness.OriginalScalarProjection

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls
open scoped BigOperators Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem factor_eq (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot),
      (∀ s, WholeCutExteriorTransport.Outside p s → left s = right s) →
      ∀ (j : DrawIndex repeats p), ¬ IsTerminal repeats p j →
        DrawSpace F2 repeats p (LeafDomain left) j =
          DrawSpace F2 repeats p (LeafDomain right) j := by
  induction p with
  | refl n =>
      intro left right hs j hj
      exact False.elim (hj True.intro)
  | @step n m i p ih =>
      intro left right hs j hj
      cases j with
      | inl j =>
          exact congrArg
            (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
              (squareSpace (space F2 branch n (LeafDomain ss)) : Type))
            (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs j)
      | inr j =>
          exact ih (childSlots left i) (childSlots right i)
            (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h)) j.2 hj

theorem scalarExterior_eq (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s) :
    OriginalTerminalSplit.ExteriorTape F2 repeats p (LeafDomain left) =
      OriginalTerminalSplit.ExteriorTape F2 repeats p (LeafDomain right) :=
  congrArg
    (fun A : OriginalTerminalSplit.ExteriorIndex repeats p → Type =>
      (j : OriginalTerminalSplit.ExteriorIndex repeats p) → A j)
    (funext (fun j => factor_eq repeats p left right hs j.val j.property))

def terminalPullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    {left right : Slots branch n → Fin t → MixedSupport.Slot}
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (values : OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain right)) :
    OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain left) :=
  fun call => HPullback (CutGroupedProjection.cutProjection p q) (values call)

def factorPullback (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (left right : Slots branch n → Fin t → MixedSupport.Slot) →
      (∀ s k, MixedSupport.Projection (left s k) (right s k)) →
      (j : DrawIndex repeats p) →
      RecursiveSampler.DrawSpace F2 repeats p (LeafDomain right) j →
        RecursiveSampler.DrawSpace F2 repeats p (LeafDomain left) j
  | _ + 1, _, .refl _, _, _, q, _, x => HPullback q x
  | _ + 1, _, .step i p, left, right, q, j, x =>
      match j with
      | Sum.inl j =>
          ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection q j.val) x
      | Sum.inr j =>
          factorPullback repeats p (childSlots left i) (childSlots right i)
            (ChildAssemblyProjection.childProjection q i) j.2 x

def tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (tape : RecursiveSampler.Tape F2 repeats p (LeafDomain right)) :
    RecursiveSampler.Tape F2 repeats p (LeafDomain left) :=
  fun j => factorPullback repeats p left right q j (tape j)

theorem evaluate_tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (tape : RecursiveSampler.Tape F2 repeats p (LeafDomain right)) (x : Domain left),
      (RecursiveSampler.evaluate F2 repeats p (LeafDomain left)
        (tapePullback repeats p left right q tape)).val x =
      (RecursiveSampler.evaluate F2 repeats p (LeafDomain right) tape).val
        (sourceProjection q x) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q tape x
          rfl
      | step i p =>
          intro left right q tape x
          simp only [RecursiveSampler.evaluate_step, RecursiveSampler.combine,
            RecursiveSampler.combineFunction, Finset.sum_apply, Pi.add_apply, Pi.mul_apply,
            PointwiseSpaces.pullback_apply]
          change
            (∑ j : OffPath i,
              (ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection q j.val)
                (tape (.inl j))).val (restrictChild left j.val x)) +
              (∑ h : Fin (repeats (n + 1)),
                (RecursiveSampler.evaluate F2 repeats p (LeafDomain (childSlots left i))
                  (tapePullback repeats p (childSlots left i) (childSlots right i)
                    (ChildAssemblyProjection.childProjection q i)
                    (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h false))).val
                      (restrictChild left i x) *
                (RecursiveSampler.evaluate F2 repeats p (LeafDomain (childSlots left i))
                  (tapePullback repeats p (childSlots left i) (childSlots right i)
                    (ChildAssemblyProjection.childProjection q i)
                    (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h true))).val
                      (restrictChild left i x)) =
            (∑ j : OffPath i, (tape (.inl j)).val (restrictChild right j.val (sourceProjection q x))) +
              (∑ h : Fin (repeats (n + 1)),
                (RecursiveSampler.evaluate F2 repeats p (LeafDomain (childSlots right i))
                  (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h false)).val
                    (restrictChild right i (sourceProjection q x)) *
                (RecursiveSampler.evaluate F2 repeats p (LeafDomain (childSlots right i))
                  (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h true)).val
                    (restrictChild right i (sourceProjection q x)))
          apply congrArg₂ (fun a b : F2 => a + b)
          · exact Finset.sum_congr rfl (fun _ _ => rfl)
          · apply Finset.sum_congr rfl
            intro h _
            apply congrArg₂ (fun a b : F2 => a * b)
            · exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h false)
                (restrictChild left i x)
            · exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h true)
                (restrictChild left i x)

theorem terminalFactor_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (call : TerminalIndex repeats p)
      (x : RecursiveSampler.DrawSpace F2 repeats p (LeafDomain right)
        (drawIndex repeats p call)),
      TerminalCalls.terminalSpaceEquiv F2 repeats p (LeafDomain left) call
          (factorPullback repeats p left right q (drawIndex repeats p call) x) =
        HPullback (CutGroupedProjection.cutProjection p q)
          (TerminalCalls.terminalSpaceEquiv F2 repeats p (LeafDomain right) call x) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q call x
          cases call
          rfl
      | step i p =>
          intro left right q call x
          exact ih p (childSlots left i) (childSlots right i)
            (ChildAssemblyProjection.childProjection q i) call.2 x

theorem exteriorFactor_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
      (_hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k)))
      (j : DrawIndex repeats p) (hj : ¬ IsTerminal repeats p j)
      (x : RecursiveSampler.DrawSpace F2 repeats p (LeafDomain right) j),
      factorPullback repeats p left right q j x =
        cast (factor_eq repeats p right left
          (fun s h => (hs s h).symm) j hj) x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q hs hk j hj x
          exact False.elim (hj True.intro)
      | step i p =>
          intro left right q hs hk j hj x
          cases j with
          | inl j =>
              exact CutProjectionGeometry.squarePullback_eq_cast
                (childSlots left j.val) (childSlots right j.val)
                (ChildAssemblyProjection.childProjection q j.val)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs j)
                (fun s k => hk (j.val, s) (WholeCutExteriorTransport.outside_ordinary i p j s) k) x
          | inr j =>
              exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
                (fun s h k => hk (i, s) (WholeCutExteriorTransport.outside_selected i p s h) k)
                j.2 hj x

theorem prefixSplit_tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (tape : RecursiveSampler.Tape F2 repeats p (LeafDomain right)) :
    OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain left)
        (tapePullback repeats p left right q tape) =
      (terminalPullback repeats p q (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain right) tape).1,
        cast (scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm))
          (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain right) tape).2) := by
  apply Prod.ext
  · funext call
    exact terminalFactor_pullback repeats p left right q call (tape (drawIndex repeats p call))
  · funext j
    exact (exteriorFactor_pullback repeats p left right q hs hk j.val j.property (tape j.val)).trans
      (CutSamplerReplayGroupingTransport.cast_pi_apply
        (scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm))
        (fun j => factor_eq repeats p right left
          (fun s h => (hs s h).symm) j.val j.property)
        (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain right) tape).2 j).symm

theorem reconstruct_pullback_apply (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (values : OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain right))
    (exterior : OriginalTerminalSplit.ExteriorTape F2 repeats p (LeafDomain right))
    (x : Domain left) :
    (OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain left)
      (fun call => HPullback (CutGroupedProjection.cutProjection p q) (values call))
      (cast (scalarExterior_eq repeats p right left
        (fun s h => (hs s h).symm)) exterior)).val x =
      (OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain right)
        values exterior).val (sourceProjection q x) := by
  let tape := (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain right)).symm
    (values, exterior)
  have hsplit :
      OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain left)
          (tapePullback repeats p left right q tape) =
        (terminalPullback repeats p q values,
          cast (scalarExterior_eq repeats p right left
            (fun s h => (hs s h).symm)) exterior) := by
    simpa only [tape, Equiv.apply_symm_apply] using
      prefixSplit_tapePullback repeats p left right q hs hk tape
  have hleft := congrArg
    (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain left)).symm hsplit
  simp only [Equiv.symm_apply_apply] at hleft
  unfold OriginalScalarReconstruction.reconstruct
  change (RecursiveSampler.evaluate F2 repeats p (LeafDomain left)
    ((OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain left)).symm
      (terminalPullback repeats p q values,
        cast (scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm)) exterior))).val x =
    (RecursiveSampler.evaluate F2 repeats p (LeafDomain right) tape).val (sourceProjection q x)
  rw [← hleft]
  exact evaluate_tapePullback repeats p left right q tape x

theorem reconstruct_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (values : OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain right))
    (exterior : OriginalTerminalSplit.ExteriorTape F2 repeats p (LeafDomain right)) :
    OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain left)
      (fun call => HPullback (CutGroupedProjection.cutProjection p q) (values call))
      (cast (scalarExterior_eq repeats p right left
        (fun s h => (hs s h).symm)) exterior) =
      HPullback q (OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain right)
        values exterior) := by
  apply Subtype.ext
  funext x
  exact reconstruct_pullback_apply repeats p left right q hs hk values exterior x

end
end PerfectCompleteness.OriginalScalarProjection

end

end OAI
