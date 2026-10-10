import Mathlib
import OAI.Computability.MinUncut.Games.HintSections
import OAI.Computability.MinUncut.Estimates.CoefficientMoments

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype Name] [Fintype I] [Fintype S] [Nonempty S]

def hintedAcceptance {q : ℕ} (strategy : HintedStrategy Name I q)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (L : Fin q → Forms (SecondAlphabet (secondQuestion U hidden pos))) : Prop :=
  projection U hidden pos
    (strategy.first U (fun k => formPullback (projection U hidden pos) (L k))) =
      strategy.second (secondQuestion U hidden pos) L

omit [Fintype Name] [Fintype S] [Nonempty S] in
lemma hintedAcceptance_generated {q : ℕ} (strategy : HintedStrategy Name I q)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (c : HintCoefficients I q) :
    hintedAcceptance strategy U hidden pos
      (hintTupleGenerator (secondQuestion U hidden pos) q c) ↔
    hintedWins strategy U hidden pos c := Iff.rfl

theorem shared_hint_soundness (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {q : ℕ} (strategy : HintedStrategy Name I q) (hidden : I → Bool) :
    (𝔼 w : I → S × Fin 3,
      𝔼 L : Fin q → Forms (SecondAlphabet
        (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
        if hintedAcceptance strategy (sampledEquations equations w) hidden
          (sampledPositions w) L then (1 : ℝ) else 0) ≤
      hintRate q ^ Fintype.card {i // hidden i=true} := by
  classical
  have hsample (w : I → S × Fin 3) :
      (𝔼 L : Fin q → Forms (SecondAlphabet
        (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
        if hintedAcceptance strategy (sampledEquations equations w) hidden
          (sampledPositions w) L then (1 : ℝ) else 0) =
      (𝔼 c : HintCoefficients I q,
        if hintedWins strategy (sampledEquations equations w) hidden
          (sampledPositions w) c then (1 : ℝ) else 0) := by
    exact (uniform_hintTupleGenerator _ q
      (fun L => if hintedAcceptance strategy (sampledEquations equations w) hidden
        (sampledPositions w) L then (1 : ℝ) else 0)).symm
  simp_rw [hsample]
  rw [Finset.expect_comm]
  calc
    _ ≤ 𝔼 c : HintCoefficients I q,
        repetitionRate ^ Fintype.card {i // Active hidden (coefficientVectors q c) i} := by
      apply Finset.expect_le_expect
      intro c _
      apply hint_fixed_coefficients_bound equations hsound strategy
        (Active hidden (coefficientVectors q c)) hidden (fun _ hi => hi.1) c
      intro k i hi
      exact congrFun hi.2 k
    _ = _ := coefficient_active_expect q hidden

lemma shared_hint_rate_vanishes (q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ n : ℕ, hintRate q ^ n < ε := by
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (hintRate_nonnegative q)
    (hintRate_lt_one q)).eventually (gt_mem_nhds hε) |>.exists

end MinUncut.Outer

end
end

end OAI
