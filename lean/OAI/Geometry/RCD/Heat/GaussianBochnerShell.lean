import OAI.Geometry.RCD.Sobolev.HessianDensityMassBound
import OAI.Geometry.RCD.Sobolev.BochnerMassExponential
import OAI.Geometry.RCD.Heat.GaussianLinearGrowth

namespace OAI

/-! # Summable Gaussian shell bounds from local Bochner measures -/

open Set Filter MeasureTheory Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [ProperSpace X]

theorem gaussian_bochner_shell_bound (p : X)
    {M V A B D Q₀ Q₁ L ℓ : ℝ}
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hQ₀ : 0 ≤ Q₀) (hQ₁ : 0 ≤ Q₁) (hL : 1 ≤ L) (hℓL : ℓ ≤ L)
    (hvol : ∀ r : ℝ, 1 ≤ r → μ.real (closedBall p (2*r)) ≤ V*Real.exp (A*r))
    (ρ H : X → ℝ) (hρD : ∀ x, ρ x ≤ D)
    (hρtail : ∀ x, ℓ ≤ dist x p → ρ x ≤ B*Real.exp (-(dist x p)^2/40))
    (j : ℕ) (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : σ.real (closedBall p (2^j*L)) ≤
      M*Real.sqrt ((1+(2^j*L)⁻¹^2)*μ.real (closedBall p (2*(2^j*L)))))
    (hH : AEStronglyMeasurable H μ)
    (hpoint : ∀ᵐ x ∂μ.restrict (closedBall p (2^j*L)),
      |H x| ≤ ρ x*(Q₀+Q₁*(dist x p)^2)*(1+(σ.rnDeriv μ x).toReal)) :
    (∫ x in dyadicShell p L j, |H x| ∂μ) ≤
      (max D B)*(Q₀+Q₁)*(V+M*(1+2*V))*L^2*
        (4:ℝ)^j*Real.exp (A*L*2^j)*gaussianShellFactor (L^2/40) j := by
  let r := (2:ℝ)^j*L
  let S := dyadicShell p L j
  have hL0 : 0 < L := by linarith
  have hj1 : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hr1 : 1 ≤ r := by dsimp only [r]; nlinarith
  have hsub : S ⊆ closedBall p r := (dyadicShell_subset_ball p L j).trans ball_subset_closedBall
  have hfin : μ (closedBall p r) ≠ ⊤ := (isCompact_closedBall p r).measure_lt_top.ne
  have hvolr : μ.real (closedBall p r) ≤ V*Real.exp (A*r) :=
    (measureReal_mono (closedBall_subset_closedBall (by linarith [hr1]))
      (isCompact_closedBall p (2*r)).measure_lt_top.ne).trans (hvol r hr1)
  have hσr := radial_mass_bound_le_exp μ p hM hA hr1 (hvol r hr1) hσ
  have hsum : μ.real S+σ.real S ≤ (V+M*(1+2*V))*Real.exp (A*r) := by
    have hm := (measureReal_mono hsub hfin).trans hvolr
    have hs := (measureReal_mono hsub (measure_ne_top σ _)).trans hσr
    nlinarith only [hm,hs]
  have hρshell (x : X) (hx : x ∈ S) :
      ρ x ≤ max D B*gaussianShellFactor (L^2/40) j := by
    cases j with
    | zero => simpa only [gaussianShellFactor,mul_one] using (hρD x).trans (le_max_left D B)
    | succ i =>
      have hd : 2^i*L ≤ dist x p := dyadicShell_separation p hL0 i hx
      have hi1 : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
      have hℓ : ℓ ≤ dist x p := hℓL.trans ((by nlinarith : L ≤ 2^i*L).trans hd)
      have hpow : ((2:ℝ)^i)^2=4^i := by rw [pow_two,← mul_pow]; norm_num
      have hs : (4:ℝ)^i*L^2 ≤ (dist x p)^2 := by
        simpa only [mul_pow,hpow] using pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^i*L) hd 2
      have he : Real.exp (-(dist x p)^2/40) ≤ gaussianShellFactor (L^2/40) (i+1) := by
        change Real.exp _ ≤ Real.exp _
        apply Real.exp_le_exp.mpr
        nlinarith only [hs]
      exact (hρtail x hℓ).trans (mul_le_mul (le_max_right D B) he
        (Real.exp_pos _).le (le_max_of_le_right hB))
  let b := max D B*(Q₀+Q₁)*r^2*gaussianShellFactor (L^2/40) j
  have hb : 0 ≤ b := mul_nonneg
    (mul_nonneg (mul_nonneg (le_max_of_le_left hD) (add_nonneg hQ₀ hQ₁)) (sq_nonneg r))
    (gaussianShellFactor_nonneg _ _)
  have hbnd : ∀ᵐ x ∂μ.restrict S, |H x| ≤ b*(1+(σ.rnDeriv μ x).toReal) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hpoint,
      ae_restrict_mem (measurableSet_dyadicShell p L j)] with x hx hm
    have hdist : dist x p ≤ r := mem_closedBall.mp (hsub hm)
    have hd2 : (dist x p)^2 ≤ r^2 := pow_le_pow_left₀ dist_nonneg hdist 2
    have hq : Q₀+Q₁*(dist x p)^2 ≤ (Q₀+Q₁)*r^2 := by
      have hmul := mul_le_mul_of_nonneg_left hd2 hQ₁
      have hr2 : 1 ≤ r^2 := by nlinarith only [hr1]
      nlinarith [mul_le_mul_of_nonneg_left hr2 hQ₀]
    apply hx.trans
    have hm := mul_le_mul (hρshell x hm) hq (add_nonneg hQ₀ (mul_nonneg hQ₁ (sq_nonneg _)))
      (mul_nonneg (le_max_of_le_left hD) (gaussianShellFactor_nonneg _ _))
    have hn := mul_le_mul_of_nonneg_right hm
      (show 0 ≤ 1+(σ.rnDeriv μ x).toReal by positivity)
    dsimp only [b]
    nlinarith only [hn]
  obtain ⟨_,hi⟩ := integral_abs_le_full_mass μ σ
    (ne_top_of_le_ne_top hfin (measure_mono hsub)) hH.restrict hb hbnd
  have hbound := hi.trans (mul_le_mul_of_nonneg_left hsum hb)
  apply hbound.trans_eq
  have hp : ((2:ℝ)^j)^2=4^j := by rw [pow_two,← mul_pow]; norm_num
  dsimp only [b,r]
  rw [mul_pow,hp,show A*((2:ℝ)^j*L)=A*L*2^j by ring]
  ring

end RegularPointCoordinates

end

end OAI
