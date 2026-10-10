import OAI.Computability.PerfectCompleteness.Construction.ChildCallNumbering
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.ChildCallNumberingLaws

noncomputable section

open scoped BigOperators Classical
open RecursiveSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]

def liftedLaw (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    FiniteDistribution (ChildCallNumbering.Raw (C := C) rows slots) :=
  (FiniteDistribution.uniform (ChildCallNumbering.Raw (C := C) rows projected)).pushforward
    (ChildCallNumbering.pullback rows p)

theorem liftedLaw_numbered (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    (liftedLaw (C := C) rows p).pushforward (ChildCallNumbering.equiv rows slots) =
      ChildBlockProjection.liftedLaw (Fintype.card C) rows p := by
  unfold liftedLaw ChildBlockProjection.liftedLaw
  rw [← ChildCallNumbering.uniform_equiv (C := C) rows projected]
  rw [FiniteDistribution.pushforward_comp, FiniteDistribution.pushforward_comp]
  congr 1

def mixtureLaw {Z : Type*} [Fintype Z] (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : Z → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ z s k, MixedSupport.Projection (slots s k) (projected z s k))
    (choiceLaw : FiniteDistribution Z) :
    FiniteDistribution (ChildCallNumbering.Raw (C := C) rows slots) :=
  choiceLaw.mixture (fun z => liftedLaw rows (p z))

theorem mixtureLaw_numbered {Z : Type*} [Fintype Z] (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : Z → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ z s k, MixedSupport.Projection (slots s k) (projected z s k))
    (choiceLaw : FiniteDistribution Z) :
    (mixtureLaw (C := C) rows slots projected p choiceLaw).pushforward
        (ChildCallNumbering.equiv rows slots) =
      ChildBlockProjection.mixtureLaw (Fintype.card C) rows slots projected p choiceLaw := by
  simp only [mixtureLaw, FiniteDistribution.pushforward_mixture,
    liftedLaw_numbered, ChildBlockProjection.mixtureLaw]

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Z : I → Type*} [∀ i, Fintype (Z i)]

def replacementLaws (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i)) :
    (i : I) → FiniteDistribution (ChildCallNumbering.Raw (C := C) rows (slots i)) :=
  fun i => mixtureLaw rows (slots i) (projected i) (p i) (choiceLaw i)

def number (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (x : (i : I) → ChildCallNumbering.Raw (C := C) rows (slots i)) :
    (i : I) → ChildBlockCardinality.Raw (Fintype.card C) rows (slots i) :=
  fun i => ChildCallNumbering.equiv rows (slots i) (x i)

def unnumber (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (x : (i : I) → ChildBlockCardinality.Raw (Fintype.card C) rows (slots i)) :
    (i : I) → ChildCallNumbering.Raw (C := C) rows (slots i) :=
  fun i => (ChildCallNumbering.equiv rows (slots i)).symm (x i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem unnumber_number (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (x : (i : I) → ChildCallNumbering.Raw (C := C) rows (slots i)) :
    unnumber rows slots (number rows slots x) = x := by
  funext i
  exact (ChildCallNumbering.equiv rows (slots i)).symm_apply_apply (x i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem number_unnumber (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (x : (i : I) → ChildBlockCardinality.Raw (Fintype.card C) rows (slots i)) :
    number rows slots (unnumber (C := C) rows slots x) = x := by
  funext i
  exact (ChildCallNumbering.equiv rows (slots i)).apply_symm_apply (x i)

theorem uniform_product_numbered (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot) :
    (FiniteProduct.law (fun i => FiniteDistribution.uniform
      (ChildCallNumbering.Raw (C := C) rows (slots i)))).pushforward (number rows slots) =
      FiniteProduct.law (fun i => FiniteDistribution.uniform
        (ChildBlockCardinality.Raw (Fintype.card C) rows (slots i))) := by
  unfold number
  rw [FiniteProduct.pushforward_map]
  congr 1
  funext i
  exact ChildCallNumbering.uniform_equiv rows (slots i)

theorem conditional_product_numbered (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i)) (mask : I → Bool) :
    (FiniteProduct.law (fun i => if mask i then
      replacementLaws (C := C) rows slots projected p choiceLaw i else
      FiniteDistribution.uniform (ChildCallNumbering.Raw (C := C) rows (slots i)))).pushforward
        (number rows slots) =
      FiniteProduct.law (fun i => if mask i then
        ChildBlockProjection.replacementLaws (Fintype.card C) rows slots projected p choiceLaw i else
        FiniteDistribution.uniform (ChildBlockCardinality.Raw (Fintype.card C) rows (slots i))) := by
  unfold number
  rw [FiniteProduct.pushforward_map]
  congr 1
  funext i
  cases mask i with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ChildCallNumbering.uniform_equiv rows (slots i)
  | true =>
      simp only [ite_true]
      exact mixtureLaw_numbered rows (slots i) (projected i) (p i) (choiceLaw i)

theorem markedLaw_numbered (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (SparseReplacement.markedLaw
      (fun i => FiniteDistribution.uniform (ChildCallNumbering.Raw (C := C) rows (slots i)))
      (replacementLaws rows slots projected p choiceLaw) β hβ hβ').pushforward
        (fun z => (z.1, number rows slots z.2)) =
      SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform
          (ChildBlockCardinality.Raw (Fintype.card C) rows (slots i)))
        (ChildBlockProjection.replacementLaws (Fintype.card C) rows slots projected p choiceLaw)
        β hβ hβ' := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward]
  unfold SparseReplacement.markedLaw
  rw [CleanConditioning.probability_kernelJoint, CleanConditioning.probability_kernelJoint]
  apply Finset.sum_congr rfl
  intro mask _
  apply congrArg (fun x : ℝ =>
    (FiniteProduct.law (fun _ : I => ProjectionPosterior.bernoulli β hβ hβ')).weight mask * x)
  have h := congrArg (fun μ => μ.probability (fun x => event (mask, x)))
    (conditional_product_numbered (C := C) rows slots projected p choiceLaw mask)
  simpa only [FiniteDistribution.probability_pushforward] using h

end
end PerfectCompleteness.ChildCallNumberingLaws

end

end OAI
