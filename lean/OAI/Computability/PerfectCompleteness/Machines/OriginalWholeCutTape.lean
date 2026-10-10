import OAI.Computability.PerfectCompleteness.Foundations.OriginalTerminalSplitLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeArraySubtreeSplit
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutCallsLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeCutSampler

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutTape

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

section Rearrangement

variable {D T C S E L O B : Type*}

def regroupStep :
    ((D → ((T → S) × E)) × ((L × ((C → S) × B)) × O)) ≃
      (((D → E) × (L × O)) × (((D × T ⊕ C) → S) × B)) where
  toFun x :=
    ((fun d => (x.1 d).2, (x.2.1.1, x.2.2)),
      (fun call => match call with
        | .inl dt => (x.1 dt.1).1 dt.2
        | .inr c => x.2.1.2.1 c,
       x.2.1.2.2))
  invFun x :=
    ((fun d => (fun terminal => x.2.1 (.inl (d, terminal)), x.1.1 d)),
      ((x.1.2.1, (fun c => x.2.1 (.inr c), x.2.2)), x.1.2.2))
  left_inv x := rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext call
        cases call <;> rfl
      · rfl

def prependUnit (A : Type*) : A ≃ Unit × A where
  toFun x := ((), x)
  invFun := Prod.snd
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨u, x⟩; cases u; rfl

end Rearrangement

variable {branch : Nat → Nat} {n m k t : Nat}

abbrev cutSlots (p : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Slots branch m → Fin t → MixedSupport.Slot :=
  fun s => slots (p.slotEmbedding s)

def Exterior (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (Slots branch n → Fin t → MixedSupport.Slot) → Type
  | _, _, .refl _, _ => Unit
  | n + 1, _, .step i p, slots =>
      (BucketSampler.Direction (rows (n + 1)) →
        OriginalTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) ×
      (Exterior rows repeats p (childSlots slots i) ×
        ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))

@[instance_reducible] def exteriorFintypeAux (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Exterior rows repeats p slots)
  | _, _, .refl _, _ => inferInstanceAs (Fintype Unit)
  | n + 1, _, .step i p, slots =>
      letI : Fintype (Exterior rows repeats p (childSlots slots i)) :=
        exteriorFintypeAux rows repeats p (childSlots slots i)
      inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) →
          OriginalTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) ×
        (Exterior rows repeats p (childSlots slots i) ×
          ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))))

instance exteriorFintype (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Exterior rows repeats p slots) := exteriorFintypeAux rows repeats p slots

def exteriorZero (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) → Exterior rows repeats p slots
  | _, _, .refl _, _ => ()
  | _, _, .step i p, slots =>
      ((fun _ j => RecursiveSampler.zeroDraw F2 repeats (.step i p) (LeafDomain slots) j.val),
        (exteriorZero rows repeats p (childSlots slots i), fun _ _ _ => 0))

instance exteriorNonempty (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Exterior rows repeats p slots) := ⟨exteriorZero rows repeats p slots⟩

abbrev BelowTape (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :=
  WholeArraySampler.Tape rows repeats q (childSlots slots chosen) ×
    ((j : RecursiveSampler.OffPath chosen) → Arrays (childSlots slots j.val) rows)

abbrev Calls (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalCutCalls.Index rows repeats p →
    RecursiveSampler.Tape F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))

def splitTape (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n (m + 1)) → (chosen : Fin (branch m)) →
      (q : Path branch m k) → (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots ≃
          Exterior rows repeats p slots ×
            (Calls rows repeats p chosen q slots ×
              BelowTape rows repeats chosen q (cutSlots p slots))
  | _, _, _, .refl _, chosen, q, slots =>
      (WholeCutSampler.stepEquiv chosen
        (WholeArraySampler.RootTape rows repeats (.step chosen q) slots)
        (WholeArraySampler.Tape rows repeats q (childSlots slots chosen))
        (fun j => Arrays (childSlots slots j.val) rows)).symm.trans (prependUnit _)
  | n + 1, _, _, .step i p, chosen, q, slots =>
      (WholeCutSampler.stepEquiv i
        (WholeArraySampler.RootTape rows repeats (.step i (p.append (.step chosen q))) slots)
        (WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows)).symm.trans
        ((Equiv.prodCongr
          (Equiv.piCongrRight (fun _ : BucketSampler.Direction (rows (n + 1)) =>
            OriginalTerminalSplit.splitTape F2 repeats (.step i p) (.step chosen q)
              (LeafDomain slots)))
          (Equiv.prodCongr (splitTape rows repeats p chosen q (childSlots slots i))
            (Equiv.refl _))).trans regroupStep)

@[simp] theorem splitTape_refl (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats (.step chosen q) slots) :
    splitTape rows repeats (.refl (m + 1)) chosen q slots ω =
      ((), (ω (.inl ()), (ω (.inr (.inl ())), fun j => ω (.inr (.inr j))))) := rfl

@[simp] theorem splitTape_step_exterior (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats ((Path.step i p).append (.step chosen q)) slots) :
    (splitTape rows repeats (.step i p) chosen q slots ω).1 =
      ((fun v => (OriginalTerminalSplit.splitTape F2 repeats (.step i p) (.step chosen q)
          (LeafDomain slots) (ω (.inl ()) v)).2),
        ((splitTape rows repeats p chosen q (childSlots slots i) (ω (.inr (.inl ())))).1,
          fun j => ω (.inr (.inr j)))) := rfl

@[simp] theorem splitTape_step_rootCall (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats ((Path.step i p).append (.step chosen q)) slots)
    (v : BucketSampler.Direction (rows (n + 1)))
    (terminal : TerminalCalls.TerminalIndex repeats (.step i p)) :
    (splitTape rows repeats (.step i p) chosen q slots ω).2.1
        (OriginalCutCalls.rootCall rows repeats i p (v, terminal)) =
      (OriginalTerminalSplit.splitTape F2 repeats (.step i p) (.step chosen q)
        (LeafDomain slots) (ω (.inl ()) v)).1 terminal := rfl

@[simp] theorem splitTape_step_lowerCall (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats ((Path.step i p).append (.step chosen q)) slots)
    (call : OriginalCutCalls.Index rows repeats p) :
    (splitTape rows repeats (.step i p) chosen q slots ω).2.1
        (OriginalCutCalls.lowerCall rows repeats i p call) =
      (splitTape rows repeats p chosen q (childSlots slots i) (ω (.inr (.inl ())))).2.1 call := rfl

@[simp] theorem splitTape_step_below (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats ((Path.step i p).append (.step chosen q)) slots) :
    (splitTape rows repeats (.step i p) chosen q slots ω).2.2 =
      (splitTape rows repeats p chosen q (childSlots slots i) (ω (.inr (.inl ())))).2.2 := rfl

def exteriorLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Exterior rows repeats p slots) := FiniteDistribution.uniform _

def callsLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Calls rows repeats p chosen q slots) :=
  FiniteProduct.law (fun _ : OriginalCutCalls.Index rows repeats p =>
    RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))

def belowLaw (rows repeats : Nat → Nat) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (BelowTape rows repeats chosen q slots) :=
  (WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen)).product
    (FiniteProduct.law (fun j : RecursiveSampler.OffPath chosen =>
      FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows)))

theorem callsLaw_uniform (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    callsLaw rows repeats p chosen q slots =
      FiniteDistribution.uniform (Calls rows repeats p chosen q slots) := by
  simp only [callsLaw, RecursiveSampler.tapeLaw_eq_uniform, UniformLinearImage.law_uniform]

theorem belowLaw_uniform (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    belowLaw rows repeats chosen q slots =
      FiniteDistribution.uniform (BelowTape rows repeats chosen q slots) := by
  rw [belowLaw, WholeArraySubtreeSplit.tapeLaw_eq_uniform, UniformLinearImage.law_uniform]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

theorem split_tapeLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
        (splitTape rows repeats p chosen q slots) =
      (exteriorLaw rows repeats p slots).product
        ((callsLaw rows repeats p chosen q slots).product
          (belowLaw rows repeats chosen q (cutSlots p slots))) := by
  rw [WholeArraySubtreeSplit.tapeLaw_eq_uniform, FiniteDistribution.pushforward_equiv,
    callsLaw_uniform, belowLaw_uniform]
  unfold exteriorLaw
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card
      (WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) : ℝ) =
    (1 / (Fintype.card (Exterior rows repeats p slots) : ℝ)) *
      ((1 / (Fintype.card (Calls rows repeats p chosen q slots) : ℝ)) *
        (1 / (Fintype.card (BelowTape rows repeats chosen q (cutSlots p slots)) : ℝ)))
  rw [Fintype.card_congr (splitTape rows repeats p chosen q slots),
    Fintype.card_prod, Fintype.card_prod]
  simp only [Nat.cast_mul, one_div, mul_inv]

end

end PerfectCompleteness.OriginalWholeCutTape

end

end OAI
