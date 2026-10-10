import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-! # Exact decomposition of finite samples by equality pattern -/

namespace Ostmann
open scoped Classical BigOperators

/-- A pattern records exactly which sampled positions coincide. Its class values
are distinct; independence is imposed only on their dominating product prior. -/
abbrev SampleEqualityPattern (I A : Type*) :=
  Σ s : Setoid I, {x : Quotient s → A // Function.Injective x}

def SampleEqualityPattern.evaluate {I A : Type*} (p : SampleEqualityPattern I A) : I → A :=
  fun i => p.2.val (Quotient.mk'' i)

theorem SampleEqualityPattern.kernel_evaluate {I A : Type*}
    (p : SampleEqualityPattern I A) : Setoid.ker p.evaluate = p.1 := by
  ext i j
  exact ⟨fun h => Quotient.exact (p.2.property h), fun h => congrArg p.2.val (Quotient.sound h)⟩

/-- Every sample has a unique equality pattern and a unique injective assignment
of values to its classes. -/
noncomputable def sampleEqualityPatternEquiv (I A : Type*) :
    SampleEqualityPattern I A ≃ (I → A) :=
  Equiv.ofBijective SampleEqualityPattern.evaluate ⟨by
    rintro ⟨s, x⟩ ⟨t, y⟩ h
    have hs : s = t := (SampleEqualityPattern.kernel_evaluate ⟨s, x⟩).symm.trans
      ((congrArg Setoid.ker h).trans (SampleEqualityPattern.kernel_evaluate ⟨t, y⟩))
    cases hs
    congr 1
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ i => exact congrFun h i,
    fun x => ⟨⟨Setoid.ker x, ⟨Setoid.kerLift x, Setoid.kerLift_injective x⟩⟩, rfl⟩⟩

@[instance_reducible] noncomputable def sampleSetoidFintype (I : Type*) [Fintype I] : Fintype (Setoid I) :=
  Fintype.ofInjective (fun s : Setoid I => {p : I × I | s p.1 p.2}) (by
    intro s t h
    ext i j
    exact Set.ext_iff.mp h (i, j))

/-- This equality is a decomposition, so no number-of-samples factor is lost. -/
theorem sum_sample_equality_patterns {I A : Type*} [Fintype I] [Fintype A]
    {M : Type*} [AddCommMonoid M] (f : (I → A) → M) :
    letI := sampleSetoidFintype I
    (∑ x : I → A, f x) =
      ∑ s : Setoid I, ∑ x : {x : Quotient s → A // Function.Injective x},
        f (fun i => x.val (Quotient.mk'' i)) := by
  let _ := sampleSetoidFintype I
  calc
    _ = ∑ p : SampleEqualityPattern I A, f p.evaluate :=
      (Equiv.sum_comp (sampleEqualityPatternEquiv I A) f).symm
    _ = _ := Fintype.sum_sigma _

end Ostmann

end OAI
