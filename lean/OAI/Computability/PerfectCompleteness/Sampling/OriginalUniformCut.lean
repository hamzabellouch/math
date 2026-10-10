import OAI.Computability.PerfectCompleteness.Sampling.OriginalUniformCutBase

namespace OAI

section

namespace PerfectCompleteness.OriginalUniformCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalUniformCutBase.valuesChildrenFintype

private theorem uniform_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (FiniteDistribution.uniform A).pushforward e = FiniteDistribution.uniform B := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport e

private theorem uniform_map_product {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (f : A → C) (g : B → D)
    (hf : (FiniteDistribution.uniform A).pushforward f = FiniteDistribution.uniform C)
    (hg : (FiniteDistribution.uniform B).pushforward g = FiniteDistribution.uniform D) :
    (FiniteDistribution.uniform (A × B)).pushforward
        (fun x => (f x.1, g x.2)) = FiniteDistribution.uniform (C × D) := by
  rw [← WholeCutSampler.uniform_product, FiniteDistribution.product_pushforward,
    hf, hg, WholeCutSampler.uniform_product]

variable {branch : Nat → Nat} {n m t : Nat}

def recordStepEquiv (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    Record rows repeats (.step i p) slots ≃
      WholeArraySampler.RootTape rows repeats (.step i p) slots ×
        (Record rows repeats p (childSlots slots i) ×
          ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows)) :=
  (OriginalWholeCutTape.regroupStep
    (D := BucketSampler.Direction (rows (n + 1)))
    (T := TerminalCalls.TerminalIndex repeats (.step i p))
    (C := OriginalCutCalls.Index rows repeats p)
    (S := H (cutSlots (.step i p) slots))
    (E := OriginalTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots))
    (L := Exterior rows repeats p (childSlots slots i))
    (O := (j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows)
    (B := BelowArrays rows p (childSlots slots i))).symm.trans
      (Equiv.prodCongr
        (Equiv.piCongrRight (fun _ : BucketSampler.Direction (rows (n + 1)) =>
          (OriginalScalarReconstruction.prefixSplit F2 repeats (.step i p)
            (LeafDomain slots)).symm))
        (Equiv.refl _))

def toStoppedTape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Record rows repeats p slots → WholeArraySampler.Tape rows repeats p slots
  | _, _, .refl _, slots, record =>
      reconstructRecord rows repeats (.refl _) slots record
  | _, _, .step i p, slots, record =>
      let split := recordStepEquiv rows repeats i p slots record
      WholeCutSampler.stepEquiv i
        (WholeArraySampler.RootTape rows repeats (.step i p) slots)
        (WholeArraySampler.Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows)
        (split.1, (toStoppedTape rows repeats p (childSlots slots i) split.2.1,
          split.2.2))

theorem evaluate_toStoppedTape (rows repeats : Nat → Nat) :
    ∀ {n m : Nat} (p : Path branch n (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (record : Record rows repeats p slots),
      WholeArraySampler.evaluate rows repeats p slots
          (toStoppedTape rows repeats p slots record) =
        reconstructRecord rows repeats p slots record := by
  intro n
  induction n with
  | zero => intro m p; cases p
  | succ n ih =>
      intro m p slots record
      cases p with
      | refl => rfl
      | step i p =>
          exact congrArg₂ (WholeArraySampler.assemble slots rows) rfl
            (congrArg (fun selected : Arrays (childSlots slots i) rows =>
              WholeArraySampler.childrenAt slots rows i selected record.1.2.2)
              (ih p (childSlots slots i)
                (record.1.2.1, ((fun call => record.2.1 (.inr call)), record.2.2))))

theorem uniform_toStoppedTape (rows repeats : Nat → Nat) :
    ∀ {n m : Nat} (p : Path branch n (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot),
      (FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
          (toStoppedTape rows repeats p slots) =
        FiniteDistribution.uniform (WholeArraySampler.Tape rows repeats p slots) := by
  intro n
  induction n with
  | zero => intro m p; cases p
  | succ n ih =>
      intro m p slots
      cases p with
      | refl =>
          exact OriginalUniformCutBase.uniform_reconstructRecord_refl rows repeats slots
      | step i p =>
          let R := WholeArraySampler.RootTape rows repeats (.step i p) slots
          let L := Record rows repeats p (childSlots slots i)
          let S := WholeArraySampler.Tape rows repeats p (childSlots slots i)
          let O := (j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows
          let e := recordStepEquiv rows repeats i p slots
          let finish := WholeCutSampler.stepEquiv i R S
            (fun j => Arrays (childSlots slots j.val) rows)
          let : Fintype (WholeArraySampler.StepTape (i := i) R S
              (fun j => Arrays (childSlots slots j.val) rows)) :=
            WholeArraySampler.tapeFintype rows repeats (.step i p) slots
          let : Nonempty (WholeArraySampler.StepTape (i := i) R S
              (fun j => Arrays (childSlots slots j.val) rows)) :=
            ⟨WholeArraySampler.zeroTape rows repeats (.step i p) slots⟩
          let middle : R × (L × O) → R × (S × O) :=
            fun z => (z.1,
              (toStoppedTape rows repeats p (childSlots slots i) z.2.1, z.2.2))
          have hinner : (FiniteDistribution.uniform (L × O)).pushforward
              (fun z => (toStoppedTape rows repeats p (childSlots slots i) z.1, z.2)) =
              FiniteDistribution.uniform (S × O) :=
            uniform_map_product (toStoppedTape rows repeats p (childSlots slots i))
              (id : O → O) (ih p (childSlots slots i))
              (FiniteDistribution.pushforward_id _)
          have hmiddle : (FiniteDistribution.uniform (R × (L × O))).pushforward middle =
              FiniteDistribution.uniform (R × (S × O)) :=
            uniform_map_product (id : R → R)
              (fun z : L × O =>
                (toStoppedTape rows repeats p (childSlots slots i) z.1, z.2))
              (FiniteDistribution.pushforward_id _) hinner
          calc
            _ = (((FiniteDistribution.uniform (Record rows repeats (.step i p) slots)).pushforward
                e).pushforward middle).pushforward finish := by
              rw [FiniteDistribution.pushforward_comp, FiniteDistribution.pushforward_comp]
              rfl
            _ = (FiniteDistribution.uniform (R × (S × O))).pushforward finish := by
              rw [uniform_equiv e, hmiddle]
            _ = _ := uniform_equiv finish

def referenceLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Record rows repeats p slots) :=
  (exteriorLaw rows repeats p slots).product
    ((FiniteProduct.law (fun _ : OriginalCutCalls.Index rows repeats p =>
        FiniteDistribution.uniform (H (cutSlots p slots)))).product
      (FiniteProduct.law (fun child : Fin (branch m) =>
        FiniteDistribution.uniform (Arrays (childSlots (cutSlots p slots) child) rows))))

theorem referenceLaw_uniform (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    referenceLaw rows repeats p slots = FiniteDistribution.uniform (Record rows repeats p slots) := by
  unfold referenceLaw exteriorLaw
  rw [UniformLinearImage.law_uniform, UniformLinearImage.law_uniform,
    WholeCutSampler.uniform_product, WholeCutSampler.uniform_product]

theorem reconstruct_referenceLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (referenceLaw rows repeats p slots).pushforward (reconstructRecord rows repeats p slots) =
      WholeArraySampler.law rows repeats p slots := by
  rw [referenceLaw_uniform]
  calc
    _ = ((FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
        (toStoppedTape rows repeats p slots)).pushforward
          (WholeArraySampler.evaluate rows repeats p slots) := by
      rw [FiniteDistribution.pushforward_comp]
      congr 1
      funext record
      exact (evaluate_toStoppedTape rows repeats p slots record).symm
    _ = (FiniteDistribution.uniform (WholeArraySampler.Tape rows repeats p slots)).pushforward
        (WholeArraySampler.evaluate rows repeats p slots) := by rw [uniform_toStoppedTape]
    _ = _ := by rw [← WholeArraySubtreeSplit.tapeLaw_eq_uniform]; rfl

end
end PerfectCompleteness.OriginalUniformCut

end

end OAI
