import OAI.Computability.PerfectCompleteness.Foundations.CutTerminalSplit
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutCallsLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeCutSampler

namespace OAI

section

namespace PerfectCompleteness.WholeCutGrouping

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

section Rearrangement

variable {V C T I E F O : Type*} {D A : I → Type*}

def regroupStep :
    ((V → ((C → (i : I) → D i) × E)) ×
      ((F × ((i : I) → (T → D i) × A i)) × O)) ≃
    (((V → E) × (F × O)) × ((i : I) → ((V × C ⊕ T) → D i) × A i)) where
  toFun x :=
    ((fun v => (x.1 v).2, (x.2.1.1, x.2.2)),
      fun i =>
        (fun q => match q with
          | .inl vc => (x.1 vc.1).1 vc.2 i
          | .inr t => (x.2.1.2 i).1 t,
         (x.2.1.2 i).2))
  invFun x :=
    ((fun v => (fun c i => (x.2 i).1 (.inl (v, c)), x.1.1 v)),
      ((x.1.2.1, fun i => (fun t => (x.2 i).1 (.inr t), (x.2 i).2)), x.1.2.2))
  left_inv x := rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      apply Prod.ext
      · funext q
        cases q <;> rfl
      · rfl

end Rearrangement

variable {branch : Nat → Nat} {n m t : Nat}

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
        CutTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) ×
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
          CutTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) ×
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
      ((fun _ j => CutSamplerRefinement.zeroFactor F2 repeats (.step i p) (LeafDomain slots) j.val),
        (exteriorZero rows repeats p (childSlots slots i), fun _ _ _ => 0))

instance exteriorNonempty (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Exterior rows repeats p slots) := ⟨exteriorZero rows repeats p slots⟩

def splitTape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      WholeCutSampler.Tape rows repeats p slots ≃
        Exterior rows repeats p slots ×
          CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) (cutSlots p slots) rows
  | _, _, .refl _, slots =>
      { toFun := fun x => ((), x)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨⟨⟩, x⟩; rfl }
  | n + 1, _, .step i p, slots =>
      (Equiv.prodCongr
        (Equiv.piCongrRight (fun _ : BucketSampler.Direction (rows (n + 1)) =>
          CutTerminalSplit.splitTape F2 repeats (.step i p) (LeafDomain slots)))
        (Equiv.prodCongr (splitTape rows repeats p (childSlots slots i)) (Equiv.refl _))).trans
          regroupStep

def exteriorLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Exterior rows repeats p slots) :=
  FiniteDistribution.uniform _

theorem split_tapeLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeCutSampler.tapeLaw rows repeats p slots).pushforward (splitTape rows repeats p slots) =
      (exteriorLaw rows repeats p slots).product
        (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) (cutSlots p slots) rows) := by
  rw [WholeCutSampler.tapeLaw_eq_uniform, FiniteDistribution.pushforward_equiv]
  unfold exteriorLaw CutChildGrouping.rawLaw
  rw [UniformLinearImage.law_uniform]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (WholeCutSampler.Tape rows repeats p slots) : ℝ) =
    (1 / (Fintype.card (Exterior rows repeats p slots) : ℝ)) *
      (1 / (Fintype.card
        (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) (cutSlots p slots) rows) : ℝ))
  rw [Fintype.card_congr (splitTape rows repeats p slots), Fintype.card_prod]
  simp only [Nat.cast_mul, one_div, mul_inv]

end
end PerfectCompleteness.WholeCutGrouping

end

end OAI
