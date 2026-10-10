import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveRieszErrorDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszDecay

namespace OAI

/-! # Uniform Riesz estimates for all characters at the ambient modulus -/

namespace Ostmann

open Filter

noncomputable def reducedRieszMain (q : ℕ) (e : Option PrimitiveComplexCharacter) (X : ℝ) : ℂ :=
  match e with
  | none => (X / 2 : ℝ)
  | some χ => canonicalCharacterRieszTerm χ q X

theorem induced_character_riesz_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
        ‖rieszTwistMean (fun n => χ (n : ZMod q)) X -
            reducedRieszMain q (primitiveCharacterReduction χ) X‖ ≤
          4 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨dp, hdp, hp⟩ := principal_riesz_sqrt_decay
  obtain ⟨dc, hdc, hc⟩ := character_riesz_canonical_sqrt_decay
  let d := min dp dc
  have hd : 0 < d := lt_min hdp hdc
  refine ⟨d, hd, ?_⟩
  filter_upwards [hp, hc, primitive_riesz_error_decay d hd,
    eventually_ge_atTop (1 : ℝ)] with X hprincipal hcharacter herror hX
  intro q hq hqX inst χ
  have hXp : 0 < X := by linarith
  have hdec (D : ℝ) (hD : d ≤ D) :
      3 * X * Real.exp (-D * Real.sqrt (Real.log X)) ≤
        3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg (Real.log X)]
  have hr : ‖reducedRieszMean (primitiveCharacterReduction χ) X -
      reducedRieszMain q (primitiveCharacterReduction χ) X‖ ≤
      3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
    cases he : primitiveCharacterReduction χ with
    | none =>
      exact hprincipal.trans (hdec dp (min_le_left _ _))
    | some ρ =>
      exact (hcharacter q hq hqX ρ (primitiveReduction_divides χ ρ he)).trans
        (hdec dc (min_le_right _ _))
  have he := (rieszTwistMean_primitive_comparison χ X hX).trans (herror q hqX)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (rieszTwistMean (fun n => χ (n : ZMod q)) X)
    (reducedRieszMean (primitiveCharacterReduction χ) X)
    (reducedRieszMain q (primitiveCharacterReduction χ) X)
  linarith

end Ostmann

end OAI
