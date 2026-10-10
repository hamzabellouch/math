import OAI.Computability.PerfectCompleteness.Foundations.CutTerminalZero
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutGrouping

namespace OAI

section

namespace PerfectCompleteness.WholeCutExteriorTransport

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def Outside (p : Path branch n m) (s : Slots branch n) : Prop :=
  s ∉ Set.range p.slotEmbedding

theorem outside_ordinary (i : Fin (branch n)) (p : Path branch n m)
    (j : OffPath i) (s : Slots branch n) : Outside (.step i p) (j.val, s) := by
  rintro ⟨u, hu⟩
  exact j.property (congrArg Prod.fst hu).symm

theorem outside_selected (i : Fin (branch n)) (p : Path branch n m)
    (s : Slots branch n) (hs : Outside p s) : Outside (.step i p) (i, s) := by
  rintro ⟨u, hu⟩
  exact hs ⟨u, congrArg Prod.snd hu⟩

theorem ordinarySlots_eq (i : Fin (branch n)) (p : Path branch n m)
    (slots target : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside (.step i p) s → slots s = target s) (j : OffPath i) :
    childSlots slots j.val = childSlots target j.val := by
  funext s
  exact hs (j.val, s) (outside_ordinary i p j s)

theorem factor_eq (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot),
      (∀ s, Outside p s → slots s = target s) →
      ∀ (j : DrawIndex repeats p), ¬ IsTerminal repeats p j →
        CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain slots) j =
          CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain target) j := by
  induction p with
  | refl n =>
      intro slots target hs j hj
      exact False.elim (hj True.intro)
  | @step n m i p ih =>
      intro slots target hs j hj
      cases j with
      | inl j =>
          exact congrArg
            (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
              (squareSpace (space F2 branch n (LeafDomain ss)) : Type))
            (ordinarySlots_eq i p slots target hs j)
      | inr j =>
          exact ih (childSlots slots i) (childSlots target i)
            (fun s h => hs (i, s) (outside_selected i p s h)) j.2 hj

theorem scalarExterior_eq (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s) :
    CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots) =
      CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain target) :=
  congrArg
    (fun A : CutTerminalSplit.ExteriorIndex repeats p → Type =>
      (j : CutTerminalSplit.ExteriorIndex repeats p) → A j)
    (funext (fun j => factor_eq repeats p slots target hs j.val j.property))

def scalarEquiv (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s) :
    CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots) ≃
      CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain target) :=
  Equiv.piCongrRight (fun j => Equiv.cast (factor_eq repeats p slots target hs j.val j.property))

@[simp] theorem scalarEquiv_apply (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s)
    (x : CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots))
    (j : CutTerminalSplit.ExteriorIndex repeats p) :
    scalarEquiv repeats p slots target hs x j =
      cast (factor_eq repeats p slots target hs j.val j.property) (x j) := rfl

theorem square_cast_eval
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (f : squareSpace (space F2 branch n (LeafDomain slots))) (x : Domain slots) :
    (cast (congrArg
        (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
          (squareSpace (space F2 branch n (LeafDomain ss)) : Type)) hs) f).val
        (cast (congrArg Domain hs) x) = f.val x := by
  cases hs
  rfl

theorem exterior_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot),
      (∀ s, Outside p s → slots s = target s) →
      WholeCutGrouping.Exterior rows repeats p slots =
        WholeCutGrouping.Exterior rows repeats p target := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl => intro slots target hs; rfl
      | step i p =>
          intro slots target hs
          have hroot := scalarExterior_eq repeats (.step i p) slots target hs
          have hselected := ih p (childSlots slots i) (childSlots target i)
            (fun s h => hs (i, s) (outside_selected i p s h))
          have hord :
              ((j : OffPath i) → Arrays (childSlots slots j.val) rows) =
                ((j : OffPath i) → Arrays (childSlots target j.val) rows) :=
            congrArg (fun A : OffPath i → Type => (j : OffPath i) → A j)
              (funext (fun j => congrArg
                (fun ss : Slots branch n → Fin t → MixedSupport.Slot => Arrays ss rows)
                (ordinarySlots_eq i p slots target hs j)))
          exact congrArg₂ (fun A B : Type => A × B)
            (congrArg (fun A : Type => BucketSampler.Direction (rows (n + 1)) → A) hroot)
            (congrArg₂ (fun A B : Type => A × B) hselected hord)

def equiv (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s) :
    WholeCutGrouping.Exterior rows repeats p slots ≃
      WholeCutGrouping.Exterior rows repeats p target :=
  Equiv.cast (exterior_eq rows repeats p slots target hs)

theorem pushforward_exteriorLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, Outside p s → slots s = target s) :
    (WholeCutGrouping.exteriorLaw rows repeats p slots).pushforward
        (equiv rows repeats p slots target hs) =
      WholeCutGrouping.exteriorLaw rows repeats p target := by
  unfold WholeCutGrouping.exteriorLaw
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (WholeCutGrouping.Exterior rows repeats p slots) : ℝ) =
    1 / (Fintype.card (WholeCutGrouping.Exterior rows repeats p target) : ℝ)
  rw [Fintype.card_congr (equiv rows repeats p slots target hs)]

end
end PerfectCompleteness.WholeCutExteriorTransport

end

section

namespace PerfectCompleteness.WholeCutZero

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n m t : Nat}

def GroupedAtClean (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots) : Prop :=
  ∀ child, clean child →
    (∀ q, ((WholeCutGrouping.splitTape rows repeats p slots tape).2 child).1 q = 0) ∧
      ∀ node row, ((WholeCutGrouping.splitTape rows repeats p slots tape).2 child).2 node row = 0

def ZeroAtClean (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → WholeCutSampler.Tape rows repeats p slots → Prop
  | _, _, .refl _, _, clean, tape =>
      ∀ child, clean child →
        (∀ q, (tape child).1 q = 0) ∧ ∀ node row, (tape child).2 node row = 0
  | _, _, .step i p, slots, clean, tape =>
      (∀ bucket, CutSamplerLocality.ZeroAtClean F2 repeats (.step i p)
        (LeafDomain slots) clean (tape.1 bucket)) ∧
      ZeroAtClean rows repeats p (childSlots slots i) clean tape.2.1

theorem grouped_step_iff (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots) :
    GroupedAtClean rows repeats (.step i p) slots clean tape ↔
      (∀ bucket terminal child, clean child →
        (CutTerminalSplit.splitTape F2 repeats (.step i p)
          (LeafDomain slots) (tape.1 bucket)).1 terminal child = 0) ∧
      GroupedAtClean rows repeats p (childSlots slots i) clean tape.2.1 := by
  constructor
  · intro h
    constructor
    · intro bucket terminal child hchild
      exact (h child hchild).1 (.inl (bucket, terminal))
    · intro child hchild
      exact ⟨fun q => (h child hchild).1 (.inr q), (h child hchild).2⟩
  · rintro ⟨hroot, hselected⟩ child hchild
    refine ⟨?_, (hselected child hchild).2⟩
    intro q
    rcases q with ⟨bucket, terminal⟩ | q
    · exact hroot bucket terminal child hchild
    · exact (hselected child hchild).1 q

theorem grouped_iff (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots),
      GroupedAtClean rows repeats p slots clean tape ↔
        ZeroAtClean rows repeats p slots clean tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots clean tape
          rfl
      | step i p =>
          intro slots clean tape
          rw [grouped_step_iff]
          exact and_congr
            (forall_congr' (fun bucket =>
              CutTerminalZero.zeroAtClean_iff F2 repeats (.step i p)
                (LeafDomain slots) clean (tape.1 bucket)))
            (ih p (childSlots slots i) clean tape.2.1)

end PerfectCompleteness.WholeCutZero

end

end OAI
