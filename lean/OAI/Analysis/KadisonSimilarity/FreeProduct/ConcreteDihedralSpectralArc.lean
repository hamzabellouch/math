import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralCutMoments

namespace OAI

/-! Construction of the published spectral-arc input for an actual finite
dihedral von Neumann algebra with its vector trace. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centeredDihedralArc_rotation_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (l : ℤ) :
    vectorTrace Ω (centeredDihedralArc (w : H →L[ℂ] H) θ * (↑(w ^ l) : H →L[ℂ] H)) =
      arcFourierIntegral θ l := by
  rw [centeredDihedralArc, sub_mul, smul_mul_assoc, one_mul, map_sub,
    ContinuousLinearMap.map_smul_of_tower,
    dihedralArcProjection_rotation_moment Ω w hw hwn hhaar,
    angularIntegral_cut_eq hθ hθπ, angularPowerMoment_zero, hhaar]
  simp only [Complex.real_smul, Complex.ofReal_div]
  ring

theorem centeredDihedralArc_reflection_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (d : H →L[ℂ] H) (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hcoset : ∀ l : ℤ, vectorTrace Ω ((↑(w ^ l) : H →L[ℂ] H) * d) = 0)
    (θ : ℝ) (l : ℤ) :
    vectorTrace Ω ((centeredDihedralArc (w : H →L[ℂ] H) θ *
      (↑(w ^ l) : H →L[ℂ] H)) * d) = 0 := by
  rw [centeredDihedralArc, sub_mul, sub_mul, smul_mul_assoc, one_mul,
    smul_mul_assoc, map_sub, ContinuousLinearMap.map_smul_of_tower,
    dihedralArcProjection_reflection_moment Ω w d hw hwn hcoset, hcoset,
    smul_zero, sub_zero]

/-- The centered arc exists in the specified von Neumann algebra, with all
moments derived from the Haar and reflection-coset laws. -/
theorem concreteDihedralSpectralArcInput (Ω : H) (P : VonNeumannAlgebra H)
    (w d : (H →L[ℂ] H)ˣ) (hwP : (w : H →L[ℂ] H) ∈ P)
    (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hd : (d : H →L[ℂ] H) * (d : H →L[ℂ] H) = 1)
    (hds : star (d : H →L[ℂ] H) = (d : H →L[ℂ] H))
    (hconj : (d : H →L[ℂ] H) * (w : H →L[ℂ] H) =
      star (w : H →L[ℂ] H) * (d : H →L[ℂ] H))
    (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, vectorTrace Ω ((↑(w ^ l) : H →L[ℂ] H) * (d : H →L[ℂ] H)) = 0) :
    DihedralSpectralArcInput (vectorTrace Ω).toLinearMap P.toStarSubalgebra w d := by
  intro θ hθ hθπ
  have hcomm : Commute (w : H →L[ℂ] H) (star (w : H →L[ℂ] H)) := by
    change (w : H →L[ℂ] H) * star (w : H →L[ℂ] H) =
      star (w : H →L[ℂ] H) * (w : H →L[ℂ] H)
    simp only [hw, ← Units.val_mul, mul_inv_cancel, inv_mul_cancel, Units.val_one]
  have ht1 : vectorTrace Ω 1 = 1 := by simpa only [zpow_zero, Units.val_one, ite_true] using hhaar 0
  have htp : vectorTrace Ω (dihedralArcProjection (w : H →L[ℂ] H) θ) =
      (θ / Real.pi : ℂ) := by
    have ht := dihedralArcProjection_rotation_moment Ω w hw hwn hhaar θ 0
    rw [zpow_zero, Units.val_one, mul_one, angularIntegral_cut_eq hθ hθπ,
      arcFourierIntegral_zero hθ hθπ, angularPowerMoment_zero] at ht
    simpa only [ite_true, mul_one, zero_add] using ht
  have htd : vectorTrace Ω (d : H →L[ℂ] H) = 0 := by
    simpa only [zpow_zero, Units.val_one, one_mul] using hcoset 0
  have htpd : vectorTrace Ω (dihedralArcProjection (w : H →L[ℂ] H) θ * (d : H →L[ℂ] H)) = 0 := by
    simpa only [zpow_zero, Units.val_one, mul_one] using
      dihedralArcProjection_reflection_moment Ω w (d : H →L[ℂ] H) hw hwn hcoset θ 0
  refine ⟨{
    element := centeredDihedralArc (w : H →L[ℂ] H) θ
    mem := centeredDihedralArc_mem P _ hwP θ
    selfAdjoint := (centeredDihedralArc_selfAdjoint _ θ).star_eq
    norm_le := centeredDihedralArc_norm_le _ hθ hθπ
    commute_rotation := centeredDihedralArc_commutes_rotation _ hcomm θ
    commute_reflection := centeredDihedralArc_commutes_reflection _ _ hd hds hconj θ
    rotation_moment := centeredDihedralArc_rotation_moment Ω w hw hwn hhaar hθ hθπ
    reflection_moment := centeredDihedralArc_reflection_moment Ω w (d : H →L[ℂ] H) hw hwn hcoset θ
    square_moment := ?_
    square_reflection_moment := ?_
  }⟩
  · have ht := centeredProjection_second_moment (vectorTrace Ω).toLinearMap
      (dihedralArcProjection (w : H →L[ℂ] H) θ)
      (dihedralArcProjection_isStarProjection _ θ).isIdempotentElem.eq (θ / Real.pi : ℂ) ht1 htp
    simp only [centeredDihedralArc, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      ContinuousLinearMap.coe_coe] using ht
  · have ht := centeredProjection_square_reflection (vectorTrace Ω).toLinearMap
      (dihedralArcProjection (w : H →L[ℂ] H) θ) (d : H →L[ℂ] H)
      (dihedralArcProjection_isStarProjection _ θ).isIdempotentElem.eq (θ / Real.pi : ℂ) htd htpd
    simp only [centeredDihedralArc, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_div, ContinuousLinearMap.coe_coe] using ht

end KadisonSimilarity

end

end OAI
