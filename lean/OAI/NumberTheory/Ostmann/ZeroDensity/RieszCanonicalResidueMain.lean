import OAI.NumberTheory.Ostmann.ZeroDensity.RieszCharacterMainSum
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszResidueError

namespace OAI

/-! # The canonical Page correction in the actual residue-class Riesz mean -/

namespace Ostmann

open Complex Filter
open scoped BigOperators

theorem real_zero_lift_inverse_nat (e : PrimitiveRealZero) (q a : ℕ) [NeZero q]
    (hd : e.modulus ∣ q) (ha : a.Coprime q) :
    (DirichletCharacter.changeLevel hd e.asRealCharacter.asComplex.character) (a : ZMod q)⁻¹ =
      (e.character (a : ZMod e.modulus) : ℂ) := by
  let τ := DirichletCharacter.changeLevel hd e.asRealCharacter.asComplex.character
  have hself : τ⁻¹ = τ := e.asRealCharacter.lift_inverse_eq hd
  have hi : τ (a : ZMod q)⁻¹ = τ (a : ZMod q) := by
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr ha
    have hh := congrArg (fun χ : DirichletCharacter ℂ q => χ (u : ZMod q)) hself
    rw [MulChar.inv_apply, Ring.inverse_unit] at hh
    rw [← hu, ZMod.inv_coe_unit]
    exact hh
  change τ (a : ZMod q)⁻¹ = _
  rw [hi]
  have hr := primitiveCharacterReduction_lift q e.asRealCharacter.asComplex hd
  exact primitiveReduction_agrees τ e.asRealCharacter.asComplex hr a ha

theorem rieszCharacterMainSum_canonical (q a : ℕ) [NeZero q] (ha : a.Coprime q) (X : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ *
      reducedRieszMain q (primitiveCharacterReduction χ) X) =
      (X / 2 : ℝ) - (pageCoefficient (actualLocalZero q) a : ℂ) *
        rieszContourWeight X (pageBeta (actualLocalZero q) : ℂ) := by
  have hua := (ZMod.isUnit_iff_coprime a q).mpr ha
  cases he : actualLocalZero q with
  | none =>
    rw [rieszCharacterMainSum_no_exception q _ hua X he]
    simp [pageCoefficient]
  | some e =>
    rw [rieszCharacterMainSum_exception q _ hua X e he]
    rw [real_zero_lift_inverse_nat e q a (actualLocalZero_spec q e he).1 ha]
    rfl

theorem canonical_riesz_residue_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ [NeZero q] (a : ℕ), a.Coprime q →
        ‖rieszResidueMean q (a : ZMod q) X - (q.totient : ℂ)⁻¹ *
            ((X / 2 : ℝ) - (pageCoefficient (actualLocalZero q) a : ℂ) *
              rieszContourWeight X (pageBeta (actualLocalZero q) : ℂ))‖ ≤
          4 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := rieszResidueMean_reduced_error
  refine ⟨d, hd, ?_⟩
  filter_upwards [h] with X hX
  intro q hq hqX inst a ha
  have hh := hX q hq hqX (a : ZMod q) ((ZMod.isUnit_iff_coprime a q).mpr ha)
  rwa [rieszCharacterMainSum_canonical q a ha X] at hh

end Ostmann

end OAI
