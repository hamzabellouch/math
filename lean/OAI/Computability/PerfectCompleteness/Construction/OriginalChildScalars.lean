import OAI.Computability.PerfectCompleteness.Construction.OriginalChildBlockProducts
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Sampling.BucketUniformLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArraySampler

namespace OAI

section

namespace PerfectCompleteness.OriginalChildScalars

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem product_swap {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward Prod.swap = ν.product μ := by
  change (μ.product ν).pushforward (Equiv.prodComm A B) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨b, a⟩
  exact mul_comm _ _

private theorem product_swap_map {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (f : B → C) :
    (μ.product ν).pushforward (fun z => (f z.2, z.1)) = (ν.pushforward f).product μ := by
  calc
    _ = ((μ.product ν).pushforward Prod.swap).pushforward (fun z => (f z.1, z.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (ν.product μ).pushforward (fun z => (f z.1, z.2)) := by rw [product_swap]
    _ = _ := by
      simpa only [id_eq, FiniteDistribution.pushforward_id] using
        FiniteDistribution.product_pushforward ν μ f (id : A → A)

variable {branch : Nat → Nat} {n m t : Nat}

abbrev Square (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (child : Fin (branch n)) := squareSpace (H (childSlots slots child))

instance squareFintype (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (child : Fin (branch n)) : Fintype (Square slots child) := Fintype.ofFinite _

def squareSum (repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n))
    (values : RecursiveSampler.CallIndex repeats n → H (childSlots slots chosen)) :
    Square slots chosen :=
  ∑ pair : Fin (repeats (n + 1)),
    RecursiveSamplerBiasAlgebra.squareProduct F2 (H (childSlots slots chosen))
      (values (pair, false)) (values (pair, true))

def specialSquareLaw (repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n)) :
    FiniteDistribution (Square slots chosen) :=
  (RecursiveSampler.callScalarLaw F2 repeats chosen q (LeafDomain slots)).pushforward
    (squareSum repeats slots chosen)

def squareComponent (repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n)) :
    (child : Fin (branch n)) → FiniteDistribution (Square slots child) :=
  ChildBlockMixture.component (specialSquareLaw repeats q slots) chosen

@[simp] theorem squareComponent_self (repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n)) :
    squareComponent repeats q slots chosen chosen = specialSquareLaw repeats q slots chosen :=
  dite_eq_left rfl

@[simp] theorem squareComponent_other (repeats : Nat → Nat) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (chosen : Fin (branch n)) (child : RecursiveSampler.OffPath chosen) :
    squareComponent repeats q slots chosen child.val = FiniteDistribution.uniform (Square slots child.val) :=
  dite_eq_right (Ne.symm child.property)

abbrev ScalarTape (repeats : Nat → Nat) (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  RecursiveSampler.Tape F2 repeats (.step chosen q) (LeafDomain slots)

def selectedAndOthers (repeats : Nat → Nat) (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) :
    Square slots chosen × ((child : RecursiveSampler.OffPath chosen) → Square slots child.val) :=
  let split := RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω
  (squareSum repeats slots chosen split.2, split.1)

def stepSquareMap (repeats : Nat → Nat) (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) : (child : Fin (branch n)) → Square slots child :=
  (Equiv.piSplitAt chosen (fun child => ↥(Square slots child))).symm
    (selectedAndOthers repeats chosen q slots ω)

theorem selectedAndOthers_law (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots)).pushforward
        (selectedAndOthers repeats chosen q slots) =
      (specialSquareLaw repeats q slots chosen).product
        (RecursiveSampler.ordinaryLaw F2 repeats chosen q (LeafDomain slots)) := by
  calc
    _ = ((RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots)).pushforward
        (RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots))).pushforward
          (fun z => (squareSum repeats slots chosen z.2, z.1)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((RecursiveSampler.ordinaryLaw F2 repeats chosen q (LeafDomain slots)).product
        (RecursiveSampler.callScalarLaw F2 repeats chosen q (LeafDomain slots))).pushforward
          (fun z => (squareSum repeats slots chosen z.2, z.1)) := by
      rw [RecursiveSampler.splitEvaluatedTape_law]
    _ = _ := product_swap_map _ _ (squareSum repeats slots chosen)

theorem squareComponent_otherLaw (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    FiniteProductSplit.otherLaw (squareComponent repeats q slots chosen) chosen =
      RecursiveSampler.ordinaryLaw F2 repeats chosen q (LeafDomain slots) := by
  apply congrArg (fun laws : (child : RecursiveSampler.OffPath chosen) →
    FiniteDistribution (Square slots child.val) => FiniteProduct.law laws)
  funext child
  exact squareComponent_other repeats q slots chosen child

theorem stepSquareMap_law (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots)).pushforward
        (stepSquareMap repeats chosen q slots) =
      FiniteProduct.law (squareComponent repeats q slots chosen) := by
  let merge :
      Square slots chosen × ((child : RecursiveSampler.OffPath chosen) → Square slots child.val) →
        (child : Fin (branch n)) → Square slots child :=
    (Equiv.piSplitAt chosen (fun child => ↥(Square slots child))).symm
  have hsplit :
      (RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots)).pushforward
          (selectedAndOthers repeats chosen q slots) =
        (squareComponent repeats q slots chosen chosen).product
          (FiniteProductSplit.otherLaw (squareComponent repeats q slots chosen) chosen) :=
    (selectedAndOthers_law repeats chosen q slots).trans
      (congrArg₂
        (fun (μ : FiniteDistribution (Square slots chosen))
            (ν : FiniteDistribution
              ((child : RecursiveSampler.OffPath chosen) → Square slots child.val)) => μ.product ν)
        (squareComponent_self repeats q slots chosen).symm
        (squareComponent_otherLaw repeats chosen q slots).symm)
  have hmerge :
      ((squareComponent repeats q slots chosen chosen).product
        (FiniteProductSplit.otherLaw (squareComponent repeats q slots chosen) chosen)).pushforward
          merge = FiniteProduct.law (squareComponent repeats q slots chosen) :=
    OriginalChildBlockProducts.merge_law (Ω := fun child => ↥(Square slots child))
      (squareComponent repeats q slots chosen) chosen
  calc
    _ = ((RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots)).pushforward
        (selectedAndOthers repeats chosen q slots)).pushforward merge :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((squareComponent repeats q slots chosen chosen).product
        (FiniteProductSplit.otherLaw (squareComponent repeats q slots chosen) chosen)).pushforward
          merge :=
      congrArg (fun μ : FiniteDistribution
          (Square slots chosen × ((child : RecursiveSampler.OffPath chosen) → Square slots child.val)) =>
        μ.pushforward merge) hsplit
    _ = _ := hmerge

def callsLaw (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Fin calls → ScalarTape repeats chosen q slots) :=
  FiniteProduct.law (fun _ : Fin calls =>
    RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots))

def callContributions (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Fin calls → ScalarTape repeats chosen q slots) :
    (child : Fin (branch n)) → Fin calls → Square slots child :=
  fun child call => stepSquareMap repeats chosen q slots (ω call) child

def callComponent (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (child : Fin (branch n)) : FiniteDistribution (Fin calls → Square slots child) :=
  FiniteProduct.law (fun _ : Fin calls => squareComponent repeats q slots chosen child)

theorem callContributions_law (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (callsLaw calls repeats chosen q slots).pushforward
        (callContributions calls repeats chosen q slots) =
      FiniteProduct.law (callComponent calls repeats chosen q slots) := by
  have hcalls : (callsLaw calls repeats chosen q slots).pushforward
      (fun ω call => stepSquareMap repeats chosen q slots (ω call)) =
      FiniteProduct.law (fun _ : Fin calls =>
        FiniteProduct.law (squareComponent repeats q slots chosen)) := by
    have h := FiniteProduct.pushforward_map
      (fun _ : Fin calls => RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots))
      (fun _ => stepSquareMap repeats chosen q slots)
    simpa only [callsLaw, stepSquareMap_law] using h
  calc
    _ = ((callsLaw calls repeats chosen q slots).pushforward
        (fun ω call => stepSquareMap repeats chosen q slots (ω call))).pushforward
          (fun x child call => x call child) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (FiniteProduct.law (fun _ : Fin calls =>
        FiniteProduct.law (squareComponent repeats q slots chosen))).pushforward
          (fun x child call => x call child) := by rw [hcalls]
    _ = _ := OriginalChildBlockProducts.transpose_law
      (fun _ : Fin calls => squareComponent repeats q slots chosen)

end
end PerfectCompleteness.OriginalChildScalars

end

end OAI
