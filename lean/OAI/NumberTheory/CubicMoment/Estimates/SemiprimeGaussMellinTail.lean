import OAI.NumberTheory.CubicMoment.Estimates.SemiprimePolynomialBounds
import OAI.NumberTheory.CubicMoment.Estimates.ZeroMellinDecay
import OAI.NumberTheory.CubicMoment.Estimates.TwoRangeSignedTail

namespace OAI

/-! The whole semiprime Gauss Mellin tail: the actual height mean is used
up to X^.13, and the elementary bound only beyond that power cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff
namespace CubicFirstMoment

lemma semiprime_far_mellin_scale {X : ℝ} (hX : 1 ≤ X) :
    X/(X^(13/100:ℝ))^2 ≤ X^(5/6:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have he : (X^(13/100:ℝ))^2 = X^(26/100:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le]
    norm_num
  rw [he]
  calc
    _ = X^(1-(26/100:ℝ)) := by rw [Real.rpow_sub hXp,Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

theorem semiprime_gauss_mellin_tail
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C₀ : ℝ} (hMV : MontgomeryVaughanBound C₀) (hC₀ : 0 ≤ C₀)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ (K : ℝ) (m : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T₀ u S : ℝ) (i j : ℕ), semiprimePartitionPiece 0 H T₀ X i j ≠ 0 →
      (1+Real.log X)^m ≤ S → |u| ≤ X^(13/100:ℝ) →
      ((∫ τ in Ici S, ‖zeroLineMellinWeight primeProductEnvelope X τ‖*
          ‖semiprimeGaussPolynomial X i j (u-τ)‖)+
       (∫ τ in Ici S, ‖zeroLineMellinWeight primeProductEnvelope X (-τ)‖*
          ‖semiprimeGaussPolynomial X i j (u+τ)‖)) ≤ K*X^(5/6:ℝ)/S := by
  obtain ⟨K₀,m,hK₀,hheight⟩ := semiprime_gauss_height_log_saving
    hpub hHuxley hperiod hMV hC₀ hGI hGQ 0
  obtain ⟨C₂,hC₂,hdecay₂⟩ := zeroLineMellinWeight_decay primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth 2
  obtain ⟨C₄,hC₄,hdecay₄⟩ := zeroLineMellinWeight_decay primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth 4
  let C := C₂+C₄
  refine ⟨4*C*(K₀+7776),m,by dsimp [C]; positivity,?_⟩
  filter_upwards [hheight,eventually_ge_atTop (1:ℝ)] with X hheight hX
  intro H T₀ u S i j hne hS hu
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hSp : 0 < S := (pow_pos (by linarith [Real.log_nonneg hX] : 0 < 1+Real.log X) m).trans_le hS
  let f := fun τ => ‖zeroLineMellinWeight primeProductEnvelope X τ‖
  let g := fun τ => ‖semiprimeGaussPolynomial X i j (u-τ)‖
  have hf : Continuous f := continuous_norm_zeroLineMellinWeight primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth hXp
  have hg : Continuous g := ((continuous_semiprimeGaussPolynomial X i j).comp
    (continuous_const.sub continuous_id)).norm
  have hg0 : ∀ τ, 0 ≤ g τ := fun _ => _root_.norm_nonneg _
  have hgb : ∀ τ, g τ ≤ 3888*X := fun τ => semiprimeGaussPolynomial_bound_of_piece hXp hne (u-τ)
  have hfi : Integrable f := (zeroLineMellinWeight_integrable primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth hXp).norm
  have hfg : Integrable (fun τ => f τ*g τ) := hfi.mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun τ => by rw [Real.norm_of_nonneg (hg0 τ)]; exact hgb τ))
  have hgood (V : ℝ) (hSV : S ≤ V) (hV : V ≤ X^(13/100:ℝ)) :
      dyadicHeightMean g V ≤ K₀*X^(5/6:ℝ) := by
    have hh := hheight H T₀ u V i j hne (hS.trans hSV) hV hu
    have he : g = fun τ => ‖semiprimeGaussPolynomial X i j (u+ -τ)‖ := by
      funext τ
      simp only [g,sub_eq_add_neg]
    rw [he,dyadicHeightMean_neg (fun τ => ‖semiprimeGaussPolynomial X i j (u+τ)‖) V]
    simpa only [pow_zero,div_one] using hh
  have hcoarse (V : ℝ) (hSV : S ≤ V) : dyadicHeightMean g V ≤ 7776*X := by
    have hh := dyadicHeightMean_le_const hg (hSp.trans_le hSV) (fun τ _ => hgb τ)
    exact hh.trans_eq (by ring)
  have hd₂ (τ : ℝ) (hτ : S ≤ |τ|) : f τ ≤ C/τ^2 := by
    have hn : τ ≠ 0 := abs_pos.mp (hSp.trans_le hτ)
    have hh := hdecay₂ X hXp τ hn
    rw [sq_abs] at hh
    exact hh.trans (div_le_div_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg τ))
  have hd₄ (τ : ℝ) (hτ : S ≤ |τ|) : f τ ≤ C/(|τ|^2*τ^2) := by
    have hn : τ ≠ 0 := abs_pos.mp (hSp.trans_le hτ)
    have hh := hdecay₄ X hXp τ hn
    have he : |τ|^4 = |τ|^2*τ^2 := by
      calc
        _ = (|τ|^2)^2 := by ring
        _ = _ := by rw [sq_abs]; ring
    rw [he] at hh
    exact hh.trans (div_le_div_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
  have hb := weighted_signed_mellin_tail_two_ranges hf hg hg0 hfg hSp
    (Real.rpow_pos_of_pos hXp _) (by positivity : 0 ≤ K₀*X^(5/6:ℝ))
    (by positivity : 0 ≤ 7776*X) (by dsimp [C]; positivity : 0 ≤ C) 2
    hgood hcoarse hd₂ hd₄
  have hs : (7776*X)*C/(X^(13/100:ℝ))^2 ≤ 7776*C*X^(5/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (semiprime_far_mellin_scale hX)
      (by dsimp [C]; positivity : 0 ≤ 7776*C)
    convert hh using 1; ring
  have hb' : ((∫ τ in Ici S, f τ*g τ)+(∫ τ in Ici S, f (-τ)*g (-τ))) ≤
      (4*C*(K₀+7776))*X^(5/6:ℝ)/S := by
    apply hb.trans
    apply div_le_div_of_nonneg_right _ hSp.le
    nlinarith
  simpa only [f,g,sub_neg_eq_add] using hb'

end CubicFirstMoment

end

end OAI
