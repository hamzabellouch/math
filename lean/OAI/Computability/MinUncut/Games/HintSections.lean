import Mathlib
import OAI.Computability.MinUncut.Estimates.OuterSampling
import OAI.Computability.MinUncut.Estimates.PatchExpectation

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I S : Type*} [Fintype Name] [Fintype I] [Fintype S] [Nonempty S]

def sampledEquations (equations : S → Equation Name) (w : I → S × Fin 3) : I → Equation Name :=
  fun j => equations (w j).1

def sampledPositions (w : I → S × Fin 3) : I → Fin 3 := fun j => (w j).2

omit [Fintype Name] [Fintype I] [Fintype S] [Nonempty S] in
lemma sampledEquations_patch (equations : S → Equation Name) (A : I → Prop)
    (bg : I → S × Fin 3) (w : {i // A i} → S × Fin 3) :
    sampledEquations equations (patch A bg w)=
      patch A (sampledEquations equations bg) (sampledEquations equations w) :=
  patch_comp A bg w (fun x => equations x.1)

omit [Fintype Name] [Fintype I] [Fintype S] [Nonempty S] in
lemma sampledPositions_patch (A : I → Prop)
    (bg : I → S × Fin 3) (w : {i // A i} → S × Fin 3) :
    sampledPositions (patch A bg w)=
      patch A (sampledPositions bg) (sampledPositions w) := patch_comp A bg w Prod.snd

theorem hint_section_bound (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {q : ℕ} (strategy : HintedStrategy Name I q)
    (A : I → Prop) (hidden : I → Bool) (hA : ∀ i, A i → hidden i=true)
    (c : HintCoefficients I q) (hzero : ∀ k i, A i → (c k).2.1 i=0)
    (bg : I → S × Fin 3) :
    (𝔼 w : {i // A i} → S × Fin 3,
      if hintedWins strategy (sampledEquations equations (patch A bg w)) hidden
        (sampledPositions (patch A bg w)) c then (1 : ℝ) else 0) ≤
      repetitionRate ^ Fintype.card {i // A i} := by
  classical
  obtain ⟨a,b,hsim⟩ := active_simulation strategy A hidden hA c hzero
    (sampledEquations equations bg) (sampledPositions bg)
  have hrep := ordinary_repetition_on equations hsound a b
  apply le_trans (b := (𝔼 w : {i // A i} → S × Fin 3,
    if (∀ j, ordinaryAccepts (equations (w j).1)
      ((equations (w j).1).names (w j).2)
      (a (fun i => equations (w i).1) j)
      (b (fun i => (equations (w i).1).names (w i).2) j)=true)
    then (1 : ℝ) else 0)) ?_ (by
    convert hrep using 1; congr 1
    exact Finset.ext (by intro x; simp))
  refine Finset.expect_le_expect (fun w _ => ?_)
  split_ifs with hw hr hr
  · rfl
  · exfalso
    apply hr
    have hwin := hw
    rw [sampledEquations_patch,sampledPositions_patch] at hwin
    exact hsim (sampledEquations equations w) (sampledPositions w) hwin
  · norm_num
  · rfl

theorem hint_fixed_coefficients_bound (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {q : ℕ} (strategy : HintedStrategy Name I q)
    (A : I → Prop) (hidden : I → Bool) (hA : ∀ i, A i → hidden i=true)
    (c : HintCoefficients I q) (hzero : ∀ k i, A i → (c k).2.1 i=0) :
    (𝔼 w : I → S × Fin 3,
      if hintedWins strategy (sampledEquations equations w) hidden
        (sampledPositions w) c then (1 : ℝ) else 0) ≤
      repetitionRate ^ Fintype.card {i // A i} :=
  expect_le_of_active_sections A _ _
    (hint_section_bound equations hsound strategy A hidden hA c hzero)

end MinUncut.Outer

end
end

end OAI
