import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarNormalizationTail
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatBoxBounds

namespace OAI

/-! A finite square approximates the actual normalization integral with
an explicit exponential error; no compact-support surrogate is used. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarNormalizationBox (L : ℝ) : ℝ :=
  ∫ x in (-L)..L, ∫ y in (-L)..L,
    planarResolventMode (planarPairEquiv.symm (x, y)) ^ 2

theorem planarPair_norm_box {L : ℝ} (hL : 0 ≤ L) {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc (-L) L ×ˢ Set.Icc (-L) L) :
    ‖planarPairEquiv.symm p‖ ≤ 2 * L := by
  have hx : p.1 ^ 2 ≤ L ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg p.1) hL).mpr (abs_le.mpr hp.1)
    simpa only [sq_abs] using h
  have hy : p.2 ^ 2 ≤ L ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg p.2) hL).mpr (abs_le.mpr hp.2)
    simpa only [sq_abs] using h
  have heq := planarPair_norm_sq p
  nlinarith [norm_nonneg (planarPairEquiv.symm p)]

theorem planarNormalizationBox_error {L : ℝ} (hL : 0 ≤ L) :
    |planarNormalizationBox L - (∫ r, planarResolventMode r ^ 2)| ≤
      1024 * Real.exp (-(1 / 2 : ℝ) * L) := by
  let f := fun p : ℝ × ℝ => planarResolventMode (planarPairEquiv.symm p) ^ 2
  let S := Set.Icc (-L) L ×ˢ Set.Icc (-L) L
  let C := planarExponentialConstant (1 / 2) ^ 2 * Real.exp (-(1 / 2 : ℝ) * L)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf : Continuous f :=
    (planarResolventMode_C7.continuous.comp planarPairEquiv_symm_continuous).pow 2
  have hfi : Integrable f := by
    apply (planarPairEquiv_measurePreserving.integrable_comp hf.aestronglyMeasurable).mp
    change Integrable (fun r : PlanarPosition =>
      planarResolventMode (planarPairEquiv.symm (planarPairEquiv r)) ^ 2)
    simpa only [MeasurableEquiv.symm_apply_apply] using planarResolventMode_square_integrable
  have hg : Continuous (fun p : ℝ × ℝ => Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)) := by
    exact Real.continuous_exp.comp (continuous_const.mul planarPairEquiv_symm_continuous.norm)
  have hgi : Integrable (fun p : ℝ × ℝ => Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)) := by
    apply (planarPairEquiv_measurePreserving.integrable_comp hg.aestronglyMeasurable).mp
    change Integrable (fun r : PlanarPosition =>
      Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm (planarPairEquiv r)‖))
    simpa only [MeasurableEquiv.symm_apply_apply] using
      planar_exp_norm_integrable (by norm_num : (0 : ℝ) < 1 / 2)
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hbox : (∫ p in S, f p) = planarNormalizationBox L := by
    change (∫ p in Set.Icc (-L) L ×ˢ Set.Icc (-L) L, f p) = _
    rw [Measure.volume_eq_prod, setIntegral_prod f hfi.integrableOn]
    simp_rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
    rfl
  have hnorm (p : ℝ × ℝ) (hp : p ∈ Sᶜ) : L ≤ ‖planarPairEquiv.symm p‖ := by
    have h0 : |p.1| ≤ ‖planarPairEquiv.symm p‖ := by
      simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
        Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 0
    have h1 : |p.2| ≤ ‖planarPairEquiv.symm p‖ := by
      simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 1
    by_contra hn
    have hn' : ‖planarPairEquiv.symm p‖ < L := lt_of_not_ge hn
    apply hp
    exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
      ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩
  have hout := setIntegral_mono_on hfi.integrableOn (hgi.const_mul C).integrableOn
    hS.compl (fun p hp => planarResolvent_square_tail_pointwise (planarPairEquiv.symm p) (hnorm p hp))
  have htotal := integral_mono_measure (μ := volume.restrict Sᶜ) Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun p =>
      mul_nonneg hC (Real.exp_pos (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)).le))
    (hgi.const_mul C)
  have heval : (∫ p : ℝ × ℝ, C * Real.exp (-(1 / 2 : ℝ) * ‖planarPairEquiv.symm p‖)) =
      planarNormalizationTailConstant * Real.exp (-(1 / 2 : ℝ) * L) := by
    rw [integral_const_mul,
      ← planarPair_integral (fun r : PlanarPosition => Real.exp (-(1 / 2 : ℝ) * ‖r‖))]
    unfold C planarNormalizationTailConstant
    ring
  have houtBound : (∫ p in Sᶜ, f p) ≤ 1024 * Real.exp (-(1 / 2 : ℝ) * L) :=
    ((hout.trans htotal).trans_eq heval).trans
      (mul_le_mul_of_nonneg_right planarNormalizationTailConstant_le (Real.exp_pos _).le)
  have hout0 : 0 ≤ ∫ p in Sᶜ, f p := integral_nonneg (fun p => sq_nonneg _)
  have heq := integral_add_compl hS hfi
  have hfull : (∫ p, f p) = ∫ r, planarResolventMode r ^ 2 :=
    (planarPair_integral (fun r => planarResolventMode r ^ 2)).symm
  rw [hbox, hfull] at heq
  rw [show planarNormalizationBox L - (∫ r, planarResolventMode r ^ 2) =
    -(∫ p in Sᶜ, f p) by linarith, abs_neg, abs_of_nonneg hout0]
  exact houtBound

end ContinuumCoulomb

end

end OAI
