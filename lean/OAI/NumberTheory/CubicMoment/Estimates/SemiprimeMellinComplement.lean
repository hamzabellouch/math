import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussMellinTail
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeLowWindow
import OAI.NumberTheory.CubicMoment.Estimates.MellinComplement

namespace OAI

/-! The actual complementary Mellin integral of the centered semiprime
polynomial. Its Gauss and model parts are bounded separately. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff
namespace CubicFirstMoment

theorem semiprime_mellin_complement
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ (K : ℝ) (m : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T₀ u S : ℝ) (i j : ℕ), semiprimePartitionPiece 0 H T₀ X i j ≠ 0 →
      (1+Real.log X)^m ≤ S → |u| ≤ X^(13/100:ℝ) →
      ‖∫ τ in (Icc (-S) S)ᶜ, zeroLineMellinWeight primeProductEnvelope X τ*
        semiprimeBlockPolynomial X i j (u-τ)‖ ≤ K*X^(5/6:ℝ)/S := by
  obtain ⟨K,m,hK,hgauss⟩ := semiprime_gauss_mellin_tail hpub hHuxley hperiod hMV hC hGI hGQ
  let M₀ := 1296*cStar*3^(5/6:ℝ)
  let M₁ := ∫ τ : ℝ, |τ| *‖zeroLineMellinWeight primeProductEnvelope 1 τ‖
  have hM₀ : 0 < M₀ := by dsimp [M₀]; have := cStar_pos; positivity
  have hM₁ : 0 ≤ M₁ := integral_nonneg (fun τ => by positivity)
  refine ⟨K+M₀*M₁,m,by positivity,?_⟩
  filter_upwards [hgauss,eventually_ge_atTop (1:ℝ)] with X hgauss hX
  intro H T₀ u S i j hne hS hu
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hSp : 0 < S := (pow_pos (by linarith [Real.log_nonneg hX] : 0 < 1+Real.log X) m).trans_le hS
  let f := fun τ => ‖zeroLineMellinWeight primeProductEnvelope X τ‖
  let g := fun τ => ‖semiprimeGaussPolynomial X i j (u-τ)‖
  let M := M₀*X^(5/6:ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hwi := zeroLineMellinWeight_integrable primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth hXp
  have hfi : Integrable f := hwi.norm
  have hfg : Integrable (fun τ => f τ*g τ) := hfi.mul_bdd
    (((continuous_semiprimeGaussPolynomial X i j).comp (continuous_const.sub continuous_id)).norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun τ => by
      rw [Real.norm_of_nonneg (_root_.norm_nonneg _)]
      exact semiprimeGaussPolynomial_bound_of_piece hXp hne (u-τ)))
  have hcenter := centered_product_mellin_integrable (semiprimeFullSupport X i)
    (semiprimeFullSupport X j) (semiprimePartitionCoefficient X i)
    (semiprimePartitionCoefficient X j) 0 primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth hXp u
  simp_rw [←semiprimeBlockPolynomial_eq_centered X i j] at hcenter
  have hcn : Integrable (fun τ => f τ*‖semiprimeBlockPolynomial X i j (u-τ)‖) := by
    simpa only [norm_mul] using hcenter.norm
  have hn : ‖∫ τ in (Icc (-S) S)ᶜ, zeroLineMellinWeight primeProductEnvelope X τ*
      semiprimeBlockPolynomial X i j (u-τ)‖ ≤
      ∫ τ in (Icc (-S) S)ᶜ, f τ*g τ+f τ*M := by
    apply (norm_integral_le_integral_norm _).trans
    have hi := integral_mono_ae (hcn.restrict (s := (Icc (-S) S)ᶜ))
      ((hfg.add (hfi.mul_const M)).restrict (s := (Icc (-S) S)ᶜ))
      (Filter.Eventually.of_forall (fun τ => by
        have hc : ‖semiprimeBlockPolynomial X i j (u-τ)‖ ≤ g τ+M := by
          rw [semiprime_centered_polynomial]
          exact (norm_sub_le _ _).trans (add_le_add le_rfl
            (semiprimeModelPolynomial_bound_of_piece hXp hne (u-τ)))
        have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ f τ from _root_.norm_nonneg _)
        simpa only [Pi.add_apply,mul_add] using hh))
    simpa only [Pi.add_apply,f,norm_mul] using hi
  have hg := hgauss H T₀ u S i j hne hS hu
  have hg' : (∫ τ in (Icc (-S) S)ᶜ, f τ*g τ) ≤ K*X^(5/6:ℝ)/S := by
    rw [integral_mellin_complement hfg hSp]
    simpa only [f,g,sub_neg_eq_add] using hg
  have hmoment := zeroLineMellinWeight_moment_integrable primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth hXp 1
  have hmom : (∫ τ : ℝ, |τ|^1*‖zeroLineMellinWeight primeProductEnvelope X τ‖) = M₁ := by
    apply integral_congr_ae
    filter_upwards with τ
    simp only [pow_one,zeroLineMellinWeight_norm primeProductEnvelope hXp,
      zeroLineMellinWeight_norm primeProductEnvelope (by norm_num : (0:ℝ) < 1)]
  have ht := weighted_height_tail _ hwi 1 hmoment hSp
  rw [hmom,pow_one] at ht
  apply hn.trans
  rw [integral_add hfg.restrict (hfi.mul_const M).restrict,integral_mul_const]
  have hb := add_le_add hg' (mul_le_mul_of_nonneg_right ht hM)
  exact hb.trans_eq (by dsimp [M]; ring)

end CubicFirstMoment

end

end OAI
