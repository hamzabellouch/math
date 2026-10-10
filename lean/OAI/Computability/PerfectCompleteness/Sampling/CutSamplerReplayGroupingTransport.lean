import OAI.Computability.PerfectCompleteness.Foundations.WholeCutExteriorTransportLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayKeys
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerKeyLocalityLemmas

namespace OAI

section

namespace PerfectCompleteness.CutSamplerReplayGroupingTransport

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls CutSamplerKeyLocality
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

universe u v

theorem cast_pi_apply {I : Type u} {A B : I → Type v}
    (h : ((i : I) → A i) = ((i : I) → B i)) (hA : ∀ i, A i = B i)
    (f : (i : I) → A i) (i : I) :
    (cast h f) i = cast (hA i) (f i) := by
  have hAB : A = B := funext hA
  cases hAB
  rfl

theorem cast_prod_fst {A A' : Type u} {B B' : Type v}
    (h : (A × B) = (A' × B')) (hA : A = A') (hB : B = B') (x : A × B) :
    (cast h x).1 = cast hA x.1 := by
  cases hA
  cases hB
  rfl

theorem cast_prod_snd {A A' : Type u} {B B' : Type v}
    (h : (A × B) = (A' × B')) (hA : A = A') (hB : B = B') (x : A × B) :
    (cast h x).2 = cast hB x.2 := by
  cases hA
  cases hB
  rfl

variable {branch : Nat → Nat} {n m t : Nat}

theorem outside_kept (p : Path branch n (m + 1)) (clean : Fin (branch m) → Prop) :
    ∀ s, WholeCutExteriorTransport.Outside p s → keptLeaf p clean s := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro s hs
          exact False.elim (hs ⟨s, rfl⟩)
      | step i p =>
          rintro ⟨j, s⟩ hs
          by_cases hji : j = i
          · subst j
            apply Or.inr
            apply ih p clean s
            rintro ⟨z, hz⟩
            exact hs ⟨z, congrArg (fun a => (i, a)) hz⟩
          · exact Or.inl hji

theorem outside_eq (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s) :
    ∀ s, WholeCutExteriorTransport.Outside p s → slots s = target s :=
  fun s hout => hs s (outside_kept p clean s hout)

theorem retainedChildSlots_eq (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (i : {i : Fin (branch m) // ¬ clean i}) :
    childSlots (WholeCutGrouping.cutSlots p slots) i.val =
      childSlots (WholeCutGrouping.cutSlots p target) i.val := by
  funext s
  exact hs (p.slotEmbedding (i.val, s)) ((keptLeaf_at_cut p clean i.val s).mpr i.property)

theorem squareEquiv_eq_cast
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (f : squareSpace (H slots)) :
    (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
        (fun s => Equiv.cast (congrArg MixedSupport.Assignment (congrFun hs s)))).symm f =
      cast (congrArg
        (fun ss : Slots branch n → Fin t → MixedSupport.Slot => (squareSpace (H ss) : Type))
        hs) f := by
  cases hs
  apply Subtype.ext
  funext x
  rfl

def castTerminal (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (terminal : CutSamplerReplayGrouping.RetainedTerminal F2 repeats p (LeafDomain slots) clean) :
    CutSamplerReplayGrouping.RetainedTerminal F2 repeats p (LeafDomain target) clean :=
  fun call child => cast (congrArg
    (fun ss : Slots branch m → Fin t → MixedSupport.Slot => (squareSpace (H ss) : Type))
    (retainedChildSlots_eq p slots target clean hs child)) (terminal call child)

theorem subExterior_cast (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots target : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf (.step i p) clean s → slots s = target s)
    (call : Fin (repeats (n + 1)) × Bool)
    (exterior : CutTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) :
    CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain target) call
        (cast (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
          (outside_eq (.step i p) slots target clean hs)) exterior) =
      cast (WholeCutExteriorTransport.scalarExterior_eq repeats p
        (childSlots slots i) (childSlots target i)
        (outside_eq p (childSlots slots i) (childSlots target i) clean
          (fun s h => hs (i, s) (Or.inr h))))
        (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain slots) call exterior) := by
  funext j
  let hext := WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
    (outside_eq (.step i p) slots target clean hs)
  let hsub := WholeCutExteriorTransport.scalarExterior_eq repeats p
    (childSlots slots i) (childSlots target i)
    (outside_eq p (childSlots slots i) (childSlots target i) clean
      (fun s h => hs (i, s) (Or.inr h)))
  change (cast hext exterior) (CutSamplerReplayGrouping.exteriorStepIndex repeats i p call j) =
    (cast hsub
      (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain slots) call exterior)) j
  rw [cast_pi_apply hext
    (fun j => WholeCutExteriorTransport.factor_eq repeats (.step i p) slots target
      (outside_eq (.step i p) slots target clean hs) j.val j.property)]
  rw [cast_pi_apply hsub
    (fun j => WholeCutExteriorTransport.factor_eq repeats p (childSlots slots i)
      (childSlots target i)
      (outside_eq p (childSlots slots i) (childSlots target i) clean
        (fun s h => hs (i, s) (Or.inr h))) j.val j.property)]
  rfl

theorem transport_assemble (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (hs : ∀ s, keptLeaf p clean s → slots s = target s)
      (exterior : CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots))
      (terminal : CutSamplerReplayGrouping.RetainedTerminal F2 repeats p (LeafDomain slots) clean),
      CutSamplerReplayTransport.transport F2 repeats p (LeafDomain slots) (LeafDomain target)
          clean (WholeCutReplayKeys.leafEquiv p slots target clean hs)
          (CutSamplerReplayGrouping.assemble F2 repeats p (LeafDomain slots) clean exterior terminal) =
        CutSamplerReplayGrouping.assemble F2 repeats p (LeafDomain target) clean
          (cast (WholeCutExteriorTransport.scalarExterior_eq repeats p slots target
            (outside_eq p slots target clean hs)) exterior)
          (castTerminal repeats p slots target clean hs terminal) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots target clean hs exterior terminal
          funext child
          exact squareEquiv_eq_cast (childSlots slots child.val) (childSlots target child.val)
            (retainedChildSlots_eq (.refl (n + 1)) slots target clean hs child) (terminal () child)
      | step i p =>
          intro slots target clean hs exterior terminal
          apply Prod.ext
          · funext j
            let hext := WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p)
              slots target (outside_eq (.step i p) slots target clean hs)
            let hslots := WholeCutExteriorTransport.ordinarySlots_eq i p slots target
              (outside_eq (.step i p) slots target clean hs) j
            change (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
                (fun s => WholeCutReplayKeys.leafEquiv (.step i p) slots target clean hs
                  (j.val, s) (Or.inl j.property))).symm
                (exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩) =
              (cast hext exterior) ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩
            rw [cast_pi_apply hext
              (fun j => WholeCutExteriorTransport.factor_eq repeats (.step i p) slots target
                (outside_eq (.step i p) slots target clean hs) j.val j.property)]
            exact squareEquiv_eq_cast (childSlots slots j.val) (childSlots target j.val) hslots
              (exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩)
          · funext call
            change CutSamplerReplayTransport.transport F2 repeats p
                (LeafDomain (childSlots slots i)) (LeafDomain (childSlots target i)) clean
                (WholeCutReplayKeys.leafEquiv p (childSlots slots i) (childSlots target i) clean
                  (fun s h => hs (i, s) (Or.inr h)))
                (CutSamplerReplayGrouping.assemble F2 repeats p (LeafDomain (childSlots slots i))
                  clean (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain slots)
                    call exterior) (fun location child => terminal (call, location) child)) =
              CutSamplerReplayGrouping.assemble F2 repeats p (LeafDomain (childSlots target i))
                clean (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain target) call
                  (cast (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
                    (outside_eq (.step i p) slots target clean hs)) exterior))
                (fun location child => castTerminal repeats (.step i p) slots target clean hs
                  terminal (call, location) child)
            rw [subExterior_cast repeats i p slots target clean hs call exterior]
            exact ih p (childSlots slots i) (childSlots target i) clean
              (fun s h => hs (i, s) (Or.inr h))
              (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain slots) call exterior)
              (fun location child => terminal (call, location) child)

end
end PerfectCompleteness.CutSamplerReplayGroupingTransport

end

end OAI
