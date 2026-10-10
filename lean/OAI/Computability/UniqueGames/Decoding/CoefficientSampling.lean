import Mathlib.Tactic.FinCases
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Soundness.SubsetIntersectionLemmas
import OAI.Computability.UniqueGames.Soundness.ZeroInformationLemmas

namespace OAI

section

/-!
Uniform raw advice coefficients obtained by discarding unused flat coordinates.
The intercept, both full columns at every position, and one singleton column at
every position are independent. For a fixed singleton set, selecting the used
columns gives exactly the uniform law on the dynamic raw coefficient type.
The identity holds for every joint test function, not merely for marginals.
-/

namespace UniqueGamesTheorem.Clean.CoefficientSampling

open Foundations.Games
open Soundness.ConditionalIncidences
open Soundness.PartnerFullSampling
open scoped BigOperators

noncomputable section

variable {P C : Type} [Fintype P] [DecidableEq P] [Fintype C] [Nonempty C]

def selectCoefficients (J : Finset P) (extra : C × (P → C × C)) (single : P → C) :
    RawCoefficients J C :=
  fun slot => match slot with
  | none => extra.1
  | some (.inl (i, j)) => if j = 0 then (extra.2 i.val).1 else (extra.2 i.val).2
  | some (.inr i) => single i.val

/-- Splitting a raw coefficient tuple into its actual independent coordinates. -/
def coefficientProductEquiv (J : Finset P) :
    RawCoefficients J C ≃ C × ((PositionOutside J → C × C) × (PositionInside J → C)) where
  toFun gamma := (gamma none,
    ((fun i => (gamma (some (.inl (i, 0))), gamma (some (.inl (i, 1))))),
      fun i => gamma (some (.inr i))))
  invFun parts := fun slot => match slot with
    | none => parts.1
    | some (.inl (i, j)) => if j = 0 then (parts.2.1 i).1 else (parts.2.1 i).2
    | some (.inr i) => parts.2.2 i
  left_inv gamma := by
    funext slot
    cases slot with
    | none => rfl
    | some slot =>
      cases slot with
      | inl pair => rcases pair with ⟨i, j⟩; fin_cases j <;> rfl
      | inr i => rfl
  right_inv parts := by
    rcases parts with ⟨intercept, full, single⟩
    rfl

/-- The complement restriction is also uniform, including an empty complement. -/
theorem expect_outside (J : Finset P) (f : (PositionOutside J → C) → ℝ) :
    (𝔼 full : P → C, f (fun j => full j.val)) =
      𝔼 outside : PositionOutside J → C, f outside := by
  calc
    _ = 𝔼 parts : (PositionInside J → C) × (PositionOutside J → C), f parts.2 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (PositionInside J → C))
          (Finset.univ : Finset (PositionOutside J → C)) (fun parts => f parts.2))

omit [Nonempty C] in
theorem expect_rawCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (𝔼 gamma : RawCoefficients J C, F gamma) =
      𝔼 intercept : C, 𝔼 full : PositionOutside J → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm (intercept, full, single)) := by
  calc
    _ = 𝔼 parts : C × ((PositionOutside J → C × C) × (PositionInside J → C)),
        F ((coefficientProductEquiv J).symm parts) :=
      Fintype.expect_equiv (coefficientProductEquiv J) _ _ (fun _ => by simp)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      apply Finset.expect_congr rfl
      intro intercept _
      rw [← Finset.univ_product_univ, Finset.expect_product]

/-- Sampling all columns and then discarding unused ones has exactly the
uniform joint law on the coefficients used by this singleton set. -/
theorem expect_selectCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (𝔼 extra : C × (P → C × C), 𝔼 single : P → C,
      F (selectCoefficients J extra single)) =
      𝔼 gamma : RawCoefficients J C, F gamma := by
  calc
    _ = 𝔼 intercept : C, 𝔼 full : P → C × C, 𝔼 single : P → C,
        F (selectCoefficients J (intercept, full) single) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = 𝔼 intercept : C, 𝔼 full : P → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm
            (intercept, (fun i => full i.val), single)) := by
      apply Finset.expect_congr rfl
      intro intercept _
      apply Finset.expect_congr rfl
      intro full _
      exact expect_restrictIndices J (fun single =>
        F ((coefficientProductEquiv J).symm (intercept, (fun i => full i.val), single)))
    _ = 𝔼 intercept : C, 𝔼 full : PositionOutside J → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm (intercept, full, single)) := by
      apply Finset.expect_congr rfl
      intro intercept _
      exact expect_outside J (fun full => 𝔼 single : PositionInside J → C,
        F ((coefficientProductEquiv J).symm (intercept, full, single)))
    _ = _ := (expect_rawCoefficients J F).symm

private theorem uniform_expectation_eq_expect {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) : (FiniteDistribution.uniform X).expectation f = 𝔼 x : X, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

theorem uniform_selectCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (FiniteDistribution.uniform (C × (P → C × C))).expectation (fun extra =>
      (FiniteDistribution.uniform (P → C)).expectation (fun single =>
        F (selectCoefficients J extra single))) =
      (FiniteDistribution.uniform (RawCoefficients J C)).expectation F := by
  simp_rw [uniform_expectation_eq_expect]
  exact expect_selectCoefficients J F

/-- The fixed-mask identity may be averaged under any independent mask law. -/
theorem mask_average_selectCoefficients (maskLaw : FiniteDistribution (Finset P))
    (F : (J : Finset P) → RawCoefficients J C → ℝ) :
    maskLaw.expectation (fun J =>
      (FiniteDistribution.uniform (C × (P → C × C))).expectation (fun extra =>
        (FiniteDistribution.uniform (P → C)).expectation (fun single =>
          F J (selectCoefficients J extra single)))) =
      maskLaw.expectation (fun J =>
        (FiniteDistribution.uniform (RawCoefficients J C)).expectation (F J)) := by
  apply FiniteDistribution.expectation_congr
  intro J
  exact uniform_selectCoefficients J (F J)

end
end UniqueGamesTheorem.Clean.CoefficientSampling

end

end OAI
