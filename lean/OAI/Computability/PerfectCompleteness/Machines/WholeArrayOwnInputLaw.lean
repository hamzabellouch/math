import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayExteriorLaw

namespace OAI

section

namespace PerfectCompleteness.WholeArrayOwnInputLaw

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open WholeArrayHiddenLaw WholeArrayExteriorLaw

noncomputable section

theorem condition_pushforward {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (f : A → B) (event : B → Bool)
    (positive : 0 < μ.probability (fun x => event (f x))) :
    (μ.condition (fun x => event (f x)) positive).pushforward f =
      (μ.pushforward f).condition event
        (by simpa only [FiniteDistribution.probability_pushforward] using positive) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton]
  simp only [FiniteDistribution.probability_pushforward,
    FiniteDistribution.probability_condition]

variable {branch : Nat → Nat} {n t : Nat}

theorem lower_ne_root (lower : Nodes branch (n + 1))
    (p : Path branch n (Nodes.height lower)) : lower ≠ Sum.inl () := by
  intro h
  have hp := p.height_le
  rw [h] at hp
  exact Nat.not_succ_le_self n hp

def rootCut (i : Fin (branch n)) (lower : Nodes branch (n + 1))
    (p : Path branch n (Nodes.height lower))
    (agree : ∀ s, (Path.step i p).slotEmbedding s = (Nodes.path lower).slotEmbedding s) :
    OwnInputReference.Cut (branch := branch) (n := n + 1) (Sum.inl ()) lower where
  proper := Nat.lt_succ_of_le p.height_le
  path := .step i p
  slots_agree := agree

def nodeCut (i : Fin (branch n)) (lower : Nodes branch n) :
    OwnInputReference.Cut (branch := branch) (n := n + 1)
      (Sum.inl ()) (Sum.inr (i, lower)) :=
  rootCut i (Sum.inr (i, lower)) (Nodes.path lower) (fun _ => rfl)

def exposedRead (rows repeats : Nat → Nat) (i : Fin (branch n))
    (lower : Nodes branch (n + 1)) (p : Path branch n (Nodes.height lower))
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (.step i p) slots) :
    HiddenBucketBias.HiddenTape W (ScalarTape repeats i p slots) ×
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
        OwnInputReference.Exterior slots rows (Sum.inl ()) lower) :=
  ((split rows repeats i p slots W ω).1,
    ((split rows repeats i p slots W ω).2.1, readExterior rows repeats i p slots lower ω))

theorem exposedRead_law (rows repeats : Nat → Nat) (i : Fin (branch n))
    (lower : Nodes branch (n + 1)) (p : Path branch n (Nodes.height lower))
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2)) :
    (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).pushforward
        (exposedRead rows repeats i lower p slots W) =
      HiddenBucketBias.exposedLaw W (scalarLaw repeats i p slots)
        (exteriorLaw rows repeats i p slots lower (lower_ne_root lower p)) :=
  split_exterior_law rows repeats i p slots lower (lower_ne_root lower p) W

def ownInput (rows repeats : Nat → Nat) (i : Fin (branch n))
    (lower : Nodes branch (n + 1)) (p : Path branch n (Nodes.height lower))
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2)) (a : Block rows lower)
    (ω : Tape rows repeats (.step i p) slots) :
    OwnInputReference.Input slots rows (Sum.inl ()) lower W a :=
  OwnInputReference.readInput slots rows (Sum.inl ()) lower W a
    (RecursiveSampler.evaluate F2 repeats (.step i p) (LeafDomain slots))
    (exposedRead rows repeats i lower p slots W ω).2

def hiddenOutput (rows repeats : Nat → Nat) (i : Fin (branch n))
    (lower : Nodes branch (n + 1)) (p : Path branch n (Nodes.height lower))
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (.step i p) slots) : W ⊗[F2] H slots :=
  HiddenBucketBias.hiddenSum W
    (RecursiveSampler.evaluate F2 repeats (.step i p) (LeafDomain slots))
    (exposedRead rows repeats i lower p slots W ω).1

theorem conditional_referenceLaw (rows repeats : Nat → Nat) (i : Fin (branch n))
    (lower : Nodes branch (n + 1)) (p : Path branch n (Nodes.height lower))
    (agree : ∀ s, (Path.step i p).slotEmbedding s = (Nodes.path lower).slotEmbedding s)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2)) (a : Block rows lower)
    (observed : OwnInputReference.Input slots rows (Sum.inl ()) lower W a)
    (positive : 0 < (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).probability
      (fun ω => decide (ownInput rows repeats i lower p slots W a ω = observed))) :
    ((WholeArraySampler.tapeLaw rows repeats (.step i p) slots).condition
      (fun ω => decide (ownInput rows repeats i lower p slots W a ω = observed)) positive).pushforward
        (hiddenOutput rows repeats i lower p slots W) =
      OwnInputReference.referenceLaw slots rows (Sum.inl ()) lower W repeats
        (rootCut i lower p agree) := by
  let eval : ScalarTape repeats i p slots → H slots :=
    RecursiveSampler.evaluate F2 repeats (.step i p) (LeafDomain slots)
  let observe := fun z :
      HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
        OwnInputReference.Exterior slots rows (Sum.inl ()) lower =>
    decide (OwnInputReference.readInput slots rows (Sum.inl ()) lower W a eval z = observed)
  let event := fun z :
      HiddenBucketBias.HiddenTape W (ScalarTape repeats i p slots) ×
        (HiddenBucketBias.VisibleTape W (ScalarTape repeats i p slots) ×
          OwnInputReference.Exterior slots rows (Sum.inl ()) lower) =>
    observe z.2
  have hevent :
      (fun ω => decide (ownInput rows repeats i lower p slots W a ω = observed)) =
        (fun ω => event (exposedRead rows repeats i lower p slots W ω)) := by
    funext ω
    exact Bool.decide_congr Iff.rfl
  have positiveRead : 0 <
      (WholeArraySampler.tapeLaw rows repeats (.step i p) slots).probability
        (fun ω => event (exposedRead rows repeats i lower p slots W ω)) := by
    rw [← hevent]
    exact positive
  have positive' : 0 <
      (HiddenBucketBias.exposedLaw W (scalarLaw repeats i p slots)
        (exteriorLaw rows repeats i p slots lower (lower_ne_root lower p))).probability event := by
    rw [← exposedRead_law rows repeats i lower p slots W,
      FiniteDistribution.probability_pushforward]
    exact positiveRead
  have hcondition :
      (((WholeArraySampler.tapeLaw rows repeats (.step i p) slots).condition
        (fun ω => decide (ownInput rows repeats i lower p slots W a ω = observed)) positive).pushforward
          (exposedRead rows repeats i lower p slots W)) =
        (HiddenBucketBias.exposedLaw W (scalarLaw repeats i p slots)
          (exteriorLaw rows repeats i p slots lower (lower_ne_root lower p))).condition
            event positive' := by
    have h := condition_pushforward
      (WholeArraySampler.tapeLaw rows repeats (.step i p) slots)
      (exposedRead rows repeats i lower p slots W) event positiveRead
    simpa only [← hevent, exposedRead_law] using h
  have href :
      ((HiddenBucketBias.exposedLaw W (scalarLaw repeats i p slots)
        (exteriorLaw rows repeats i p slots lower (lower_ne_root lower p))).condition
          event positive').pushforward
            (fun z => HiddenBucketBias.hiddenSum W eval z.1) =
        HiddenBucketBias.law W (scalarLaw repeats i p slots) eval :=
    HiddenBucketBias.law_condition_exterior W (scalarLaw repeats i p slots)
      (exteriorLaw rows repeats i p slots lower (lower_ne_root lower p))
      eval observe positive'
  calc
    _ = (((WholeArraySampler.tapeLaw rows repeats (.step i p) slots).condition
        (fun ω => decide (ownInput rows repeats i lower p slots W a ω = observed)) positive).pushforward
          (exposedRead rows repeats i lower p slots W)).pushforward
            (fun z => HiddenBucketBias.hiddenSum W eval z.1) :=
      (FiniteDistribution.pushforward_comp _ (exposedRead rows repeats i lower p slots W)
        (fun z => HiddenBucketBias.hiddenSum W eval z.1)).symm
    _ = HiddenBucketBias.law W (scalarLaw repeats i p slots) eval := by
      rw [hcondition]
      exact href
    _ = _ := rfl

theorem conditional_referenceLaw_node (rows repeats : Nat → Nat) (i : Fin (branch n))
    (lower : Nodes branch n)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (a : Block (branch := branch) (n := n + 1) rows (Sum.inr (i, lower)))
    (observed : OwnInputReference.Input slots rows (Sum.inl ()) (Sum.inr (i, lower)) W a)
    (positive : 0 <
      (WholeArraySampler.tapeLaw rows repeats (.step i (Nodes.path lower)) slots).probability
        (fun ω => decide (ownInput rows repeats i (Sum.inr (i, lower)) (Nodes.path lower)
          slots W a ω = observed))) :
    ((WholeArraySampler.tapeLaw rows repeats (.step i (Nodes.path lower)) slots).condition
      (fun ω => decide (ownInput rows repeats i (Sum.inr (i, lower)) (Nodes.path lower)
        slots W a ω = observed)) positive).pushforward
          (hiddenOutput rows repeats i (Sum.inr (i, lower)) (Nodes.path lower) slots W) =
      OwnInputReference.referenceLaw slots rows (Sum.inl ()) (Sum.inr (i, lower)) W repeats
        (nodeCut i lower) :=
  conditional_referenceLaw rows repeats i (Sum.inr (i, lower)) (Nodes.path lower)
    (fun _ => rfl) slots W a observed positive

end
end PerfectCompleteness.WholeArrayOwnInputLaw

end

end OAI
