import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernelLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

abbrev Physical (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :=
  Σ b : Bool, Block C rows (mixedSlots clauses designated i s b)

def physical (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i) :
    Physical (C := C) (t := t) rows clauses designated i s :=
  ⟨rawProjected rows clauses designated i raw,
    decodeRight rows clauses designated i s raw⟩

@[simp] theorem physical_inl (i : Fin (branch n))
    (s : Source (m := m) (t := t) designated i)
    (raw : D (C := C) (t := t) rows clauses designated i) :
    physical rows clauses designated i s (.inl raw) =
      (⟨false, decodeNative rows clauses designated i s raw⟩ :
        Physical (C := C) (t := t) rows clauses designated i s) := rfl

@[simp] theorem physical_inr (i : Fin (branch n))
    (s : Source (m := m) (t := t) designated i)
    (raw : UniformLatent.Raw (Factors (C := C) (t := t) rows clauses designated i)) :
    physical rows clauses designated i s (.inr raw) =
      (⟨true, decodeProjected rows clauses designated i s raw⟩ :
        Physical (C := C) (t := t) rows clauses designated i s) := rfl

def physicalLaw (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (Physical (C := C) (t := t) rows clauses designated i s) :=
  (flag i).mixture (fun b =>
    (FiniteDistribution.uniform (Block C rows (mixedSlots clauses designated i s b))).pushforward
      (fun block => (⟨b, block⟩ : Physical (C := C) (t := t) rows clauses designated i s)))

theorem kernel_physical (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (kernel (C := C) (t := t) rows clauses designated flag i s).pushforward
        (physical rows clauses designated i s) =
      physicalLaw (C := C) (t := t) rows clauses designated flag i s := by
  unfold kernel UniformLatent.projectedKernel physicalLaw
  rw [FiniteDistribution.pushforward_mixture]
  apply congrArg (fun laws : Bool →
    FiniteDistribution (Physical (C := C) (t := t) rows clauses designated i s) =>
      (flag i).mixture laws)
  funext b
  cases b with
  | false =>
      change ((nonprojected (C := C) (t := t) rows clauses designated i s).pushforward
        Sum.inl).pushforward (physical rows clauses designated i s) =
          (FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s)).pushforward
            (fun block => (⟨false, block⟩ : Physical (C := C) (t := t) rows clauses designated i s))
      rw [FiniteDistribution.pushforward_comp]
      calc
        _ = ((nonprojected (C := C) (t := t) rows clauses designated i s).pushforward
            (decodeNative rows clauses designated i s)).pushforward
              (fun block => (⟨false, block⟩ :
                Physical (C := C) (t := t) rows clauses designated i s)) :=
          (FiniteDistribution.pushforward_comp _ _ _).symm
        _ = _ := by rw [decodeNative_law]
  | true =>
      change ((UniformLatent.latentKernel
        (Factors (C := C) (t := t) rows clauses designated i) s).pushforward
          Sum.inr).pushforward (physical rows clauses designated i s) =
            (FiniteDistribution.uniform
              (Projected (C := C) (t := t) rows clauses designated i s)).pushforward
                (fun block => (⟨true, block⟩ : Physical (C := C) (t := t) rows clauses designated i s))
      rw [FiniteDistribution.pushforward_comp]
      calc
        _ = ((UniformLatent.latentKernel
            (Factors (C := C) (t := t) rows clauses designated i) s).pushforward
              (decodeProjected rows clauses designated i s)).pushforward
                (fun block => (⟨true, block⟩ :
                  Physical (C := C) (t := t) rows clauses designated i s)) :=
          (FiniteDistribution.pushforward_comp _ _ _).symm
        _ = _ := by rw [decodeProjected_law]

theorem kernels_physical (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (fun raw i => physical rows clauses designated i (sources i) (raw i)) =
      FiniteProduct.law (fun i =>
        physicalLaw (C := C) (t := t) rows clauses designated flag i (sources i)) := by
  rw [FiniteProduct.pushforward_map]
  exact congrArg FiniteProduct.law
    (funext fun i => kernel_physical rows clauses designated flag i (sources i))

end
end PerfectCompleteness.SourceChildKernelLaw

end

end OAI
