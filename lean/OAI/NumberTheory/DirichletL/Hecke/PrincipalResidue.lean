import OAI.NumberTheory.DirichletL.Hecke.RayFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrincipalResidue
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem coefficients_sum_positive (χ : Character) (hχ : χ.residue=1) :
    ∃ c : ℝ, 0<c ∧ (∑ a, coefficients χ a)=(c : ℂ) := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  have heq : (∑ a, coefficients χ a) =
      (Nat.card (coordinateQuotientHom χ).ker : ℂ) *
        (Fintype.card (O ⧸ χ.modulus)ˣ : ℂ) := by
    calc
      _ = ∑ a, χ.residue (coordinateQuotientHom χ (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact coefficients_eq_quotient_character χ a
      _ = ∑ a : ZMod χ.period × ZMod χ.period,
          χ.residue (coordinateQuotientHom χ a) :=
        e.bijective.sum_comp (fun a => χ.residue (coordinateQuotientHom χ a))
      _ = _ := by
        rw [sum_comp_additiveHom _ (coordinateQuotientHom_surjective χ), hχ,
          MulChar.sum_one_eq_card_units]
  refine ⟨(Nat.card (coordinateQuotientHom χ).ker : ℝ) * Fintype.card (O ⧸ χ.modulus)ˣ, ?_, ?_⟩
  · exact mul_pos (Nat.cast_pos.mpr (Nat.card_pos (α := (coordinateQuotientHom χ).ker)))
      (Nat.cast_pos.mpr (Fintype.card_pos (α := (O ⧸ χ.modulus)ˣ)))
  · simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using heq

theorem principal_residue_positive (χ : Character) (hχ : χ.residue=1) :
    ∃ R : ℝ, 0<R ∧ HeckeOrigin.poleRemoved χ 1=(R : ℂ) := by
  obtain ⟨c,hc,he⟩ := coefficients_sum_positive χ hχ
  have hN : (0 : ℝ)<χ.period := Nat.cast_pos.mpr (NeZero.pos χ.period)
  let d : ℝ := (((χ.period : ℝ)^2)^(-(1/2 : ℝ))) *
    ((3*(χ.period : ℝ)^2)^(-(1/2 : ℝ)))
  have hd : 0<d := mul_pos (Real.rpow_pos_of_pos (sq_pos_of_pos hN) _)
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hN)) _)
  refine ⟨Real.pi*(2*d*c)/6, by positivity, ?_⟩
  rw [HeckeOrigin.poleRemoved_one, HeckeReciprocal.regularizedL_at_one,
    HeckeTheta.pair_g₀, he]
  simp only [HeckeTheta.dualScalar, d, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]

theorem fixed_principal_residue_positive (M : Ideal O) [NeZero M] :
    ∃ R : ℝ, 0<R ∧ HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1) 1=(R : ℂ) :=
  principal_residue_positive _ rfl

end SevenEighths.HeckePrincipalResidue

end

end OAI
