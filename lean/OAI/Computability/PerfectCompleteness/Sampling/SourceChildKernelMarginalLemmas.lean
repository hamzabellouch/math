import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildKernelLaw

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernelMarginal

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces SourceQuestionReconstruction

noncomputable section

theorem nestedKernel_sources {E R T : Type*} [Fintype E] [Fintype R] [Fintype T]
    (μ : FiniteDistribution E) (ν : FiniteDistribution R)
    (kernel : E → R → FiniteDistribution T) :
    (CleanConditioning.kernelJoint μ (fun e => CleanConditioning.kernelJoint ν (kernel e))).pushforward
        (fun x => (x.1, x.2.1)) = μ.product ν := by
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨e, r⟩
  simp only [FiniteDistribution.pushforward, CleanConditioning.kernelJoint,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  rw [Finset.sum_eq_single e]
  · rw [Finset.sum_eq_single r]
    · simp [← Finset.mul_sum, FiniteDistribution.normalized]
    · intro r' _ hne
      simp [hne]
    · simp
  · intro e' _ hne
    simp [hne]
  · simp

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

def sources (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    SourceChildKernel.Sources (m := m) (t := t) designated :=
  fun i => ((sample i).1, (sample i).2.1)

theorem childrenLaw_sources (rows : Nat → Nat)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) →
      FiniteDistribution (SourceChildKernel.Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.childrenLaw (C := C) rows clauses designated μ ν flag).pushforward
        (sources rows clauses designated) =
      FiniteProduct.law (fun i => (μ i).product (ν i)) := by
  let P (i : Fin (branch n)) : FiniteDistribution
      (SourceTuple m t × (SourceChildKernel.Rest (m := m) (t := t) designated i ×
        SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)) :=
    CleanConditioning.kernelJoint (μ i) (fun e => CleanConditioning.kernelJoint (ν i)
      (fun r => SourceChildKernel.kernel rows clauses designated flag i (e, r)))
  let f (i : Fin (branch n))
      (x : SourceTuple m t × (SourceChildKernel.Rest (m := m) (t := t) designated i ×
        SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)) :
      SourceChildKernel.Source (m := m) (t := t) designated i := (x.1, x.2.1)
  change (FiniteProduct.law P).pushforward (fun sample i => f i (sample i)) = _
  refine (CleanConditioning.pushforward_law P f).trans ?_
  apply congrArg (fun laws : (i : Fin (branch n)) →
    FiniteDistribution (SourceChildKernel.Source (m := m) (t := t) designated i) =>
      FiniteProduct.law laws)
  funext i
  exact nestedKernel_sources (μ i) (ν i)
    (fun e r => SourceChildKernel.kernel rows clauses designated flag i (e, r))

theorem originalLaw_sources [NeZero m] (rows : Nat → Nat)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (sources rows clauses designated) =
      FiniteProduct.law (fun i : Fin (branch n) =>
        (SourceOddLists.tupleLaw m t).product
          (FiniteProduct.law (fun _ : {leaf : Slots branch n // leaf ≠ designated i} =>
            SourceOddLists.tupleLaw m t))) :=
  childrenLaw_sources rows clauses designated _ _ flag

end
end PerfectCompleteness.SourceChildKernelMarginal

end

section

namespace PerfectCompleteness.SourceChildNativeLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel
open scoped Classical

noncomputable section

def falseFlag : FiniteDistribution Bool where
  weight b := if b then 0 else 1
  nonnegative b := by cases b <;> simp
  normalized := by simp

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def pullback (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) (b : Bool)
    (block : Block C rows (mixedSlots clauses designated i s b)) :
    Native (C := C) (t := t) rows clauses designated i s :=
  (fun call => ChildBlockProjection.squarePullback (projection clauses designated i s b)
      (block.1 call),
    ChildBlockProjection.arraysPullback rows (projection clauses designated i s b) block.2)

omit [Fintype C] in
@[simp] theorem pullback_false (i : Fin (branch n))
    (s : Source (m := m) (t := t) designated i)
    (block : Native (C := C) (t := t) rows clauses designated i s) :
    pullback rows clauses designated i s false block = block := by
  apply Prod.ext
  · funext call
    apply Subtype.ext
    funext x
    rfl
  · funext node row
    apply Subtype.ext
    funext x
    rfl

def physicalLeft (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (x : SourceChildKernelLaw.Physical (C := C) (t := t) rows clauses designated i s) :
    Native (C := C) (t := t) rows clauses designated i s :=
  pullback rows clauses designated i s x.1 x.2

def decodeLeft (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i) :
    Native (C := C) (t := t) rows clauses designated i s :=
  physicalLeft rows clauses designated i s
    (SourceChildKernelLaw.physical rows clauses designated i s raw)

theorem decodeLeft_eq_leftChildren (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i)
    (i : Fin (branch n)) :
    decodeLeft rows clauses designated i (sources i) (raw i) =
      leftChildren rows clauses designated sources raw i := rfl

def leftLaw (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (Native (C := C) (t := t) rows clauses designated i s) :=
  (flag i).mixture (fun b => if b then
    (FiniteDistribution.uniform (Projected (C := C) (t := t) rows clauses designated i s)).pushforward
      (pullback rows clauses designated i s true)
    else FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s))

theorem physicalLaw_left (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (SourceChildKernelLaw.physicalLaw (C := C) (t := t) rows clauses designated flag i s).pushforward
        (physicalLeft rows clauses designated i s) =
      leftLaw (C := C) (t := t) rows clauses designated flag i s := by
  unfold SourceChildKernelLaw.physicalLaw leftLaw
  rw [FiniteDistribution.pushforward_mixture]
  apply congrArg (fun laws : Bool →
    FiniteDistribution (Native (C := C) (t := t) rows clauses designated i s) =>
      (flag i).mixture laws)
  funext b
  cases b with
  | false =>
      rw [FiniteDistribution.pushforward_comp]
      calc
        _ = (FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s)).pushforward
            (id : Native (C := C) (t := t) rows clauses designated i s → _) := by
          apply congrArg (fun f : Native (C := C) (t := t) rows clauses designated i s →
            Native (C := C) (t := t) rows clauses designated i s =>
              (FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s)).pushforward f)
          funext block
          exact pullback_false rows clauses designated i s block
        _ = _ := UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
          (FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s))
  | true =>
      exact FiniteDistribution.pushforward_comp _ _ _

theorem kernel_decodeLeft (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (kernel (C := C) (t := t) rows clauses designated flag i s).pushforward
        (decodeLeft rows clauses designated i s) =
      leftLaw (C := C) (t := t) rows clauses designated flag i s := by
  calc
    _ = ((kernel (C := C) (t := t) rows clauses designated flag i s).pushforward
        (SourceChildKernelLaw.physical rows clauses designated i s)).pushforward
          (physicalLeft rows clauses designated i s) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by rw [SourceChildKernelLaw.kernel_physical, physicalLaw_left]

theorem leftLaw_false (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    leftLaw (C := C) (t := t) rows clauses designated (fun _ => falseFlag) i s =
      FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro block
  simp [leftLaw, falseFlag, FiniteDistribution.mixture]

theorem kernel_decodeLeft_false (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (kernel (C := C) (t := t) rows clauses designated (fun _ => falseFlag) i s).pushforward
        (decodeLeft rows clauses designated i s) =
      FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s) := by
  rw [kernel_decodeLeft, leftLaw_false]

theorem kernels_decodeLeft (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i => kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (fun raw i => decodeLeft rows clauses designated i (sources i) (raw i)) =
      FiniteProduct.law (fun i => leftLaw (C := C) (t := t) rows clauses designated flag i (sources i)) := by
  rw [FiniteProduct.pushforward_map]
  exact congrArg FiniteProduct.law
    (funext fun i => kernel_decodeLeft rows clauses designated flag i (sources i))

theorem kernels_leftChildren (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i => kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (leftChildren rows clauses designated sources) =
      FiniteProduct.law (fun i => leftLaw (C := C) (t := t) rows clauses designated flag i (sources i)) :=
  kernels_decodeLeft rows clauses designated flag sources

theorem kernels_leftChildren_false (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i => kernel (C := C) (t := t) rows clauses designated
      (fun _ => falseFlag) i (sources i))).pushforward
        (leftChildren rows clauses designated sources) =
      FiniteProduct.law (fun i =>
        FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i (sources i))) := by
  rw [kernels_leftChildren]
  exact congrArg FiniteProduct.law
    (funext fun i => leftLaw_false rows clauses designated i (sources i))

end
end PerfectCompleteness.SourceChildNativeLaw

end

end OAI
