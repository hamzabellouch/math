import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarMultiwellScale

namespace OAI

/-! A global multiwell lower bound on every test function, with actual
uncut orbital coefficients. This form of the estimate is stable under H1
approximation and tensor products; no exact orthogonality of approximants
is needed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

private theorem cutoff_add_sq_le {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    (a+b)^2 ≤ (1+η)*a^2 + (1+η⁻¹)*b^2 := by
  have he : (((1+η)*a^2 + (1+η⁻¹)*b^2) - (a+b)^2)*η = (η*a-b)^2 := by
    field_simp [hη.ne']
    ring
  have hn : 0 ≤ (((1+η)*a^2 + (1+η⁻¹)*b^2) - (a+b)^2)*η := by
    rw [he]
    exact sq_nonneg _
  exact sub_nonneg.mp ((nonneg_of_mul_nonneg_left hn hη))

theorem planarSiteCutoff_pair_error {D : ℝ} (hD : 0 < D) (u : PlanarPosition)
    (f : PlanarPosition → ℝ) (hf : MemLp f 2) :
    ((∫ x, (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u)) -
      (∫ x, f x*normalizedPlanarMode (x-u)))^2 ≤
      (∫ x, f x^2)*(planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))) := by
  have hm := normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  have hi₀ : Integrable (fun x => f x*normalizedPlanarMode (x-u)) := hf.integrable_mul hm
  have hi₁ : Integrable (fun x => f x*planarSiteCutoffError D u x) :=
    hf.integrable_mul (planarSiteCutoffError_memLp D u)
  have he : (∫ x, (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u)) -
      (∫ x, f x*normalizedPlanarMode (x-u)) = ∫ x, f x*planarSiteCutoffError D u x := by
    have hp : (fun x => (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u)) =
        (fun x => f x*normalizedPlanarMode (x-u) + f x*planarSiteCutoffError D u x) := by
      funext x
      unfold planarSiteCutoffError
      ring
    rw [hp, integral_add hi₀ hi₁]
    ring
  rw [he]
  exact (planar_l2_pair_sq_le f (planarSiteCutoffError D u) hf
    (planarSiteCutoffError_memLp D u)).trans
      (mul_le_mul_of_nonneg_left (planarSiteCutoffError_integral_bound hD u)
        (integral_nonneg (fun x => sq_nonneg _)))

theorem planarSiteCutoff_pair_bound {D η : ℝ} (hD : 0 < D) (hη : 0 < η)
    (u : PlanarPosition) (f : PlanarPosition → ℝ) (hf : MemLp f 2) :
    (∫ x, (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u))^2 ≤
      (1+η)*(∫ x, f x*normalizedPlanarMode (x-u))^2 +
      (1+η⁻¹)*(∫ x, f x^2)*(planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))) := by
  have hy := cutoff_add_sq_le hη (∫ x, f x*normalizedPlanarMode (x-u))
    ((∫ x, (Real.sin (planarSiteAngle D u x)*f x)*normalizedPlanarMode (x-u)) -
      (∫ x, f x*normalizedPlanarMode (x-u)))
  have he := mul_le_mul_of_nonneg_left (planarSiteCutoff_pair_error hD u f hf)
    (show 0 ≤ 1+η⁻¹ by positivity)
  nlinarith

/-- Global lower bound with explicitly controlled finite orbital form and
cutoff error. The only spectral input is the published isolated-well gap. -/
theorem planarWellSum_test_projection_bound
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η : ℝ), 8 ≤ D → 0 < η →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      ∀ f : PlanarPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2:ℝ)+γ-planarSiteDerivativeBound D^2-
        γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)))*(∫ x, f x^2) -
        γ*(1+η)*(∑ i, (∫ x, f x*normalizedPlanarMode (x-u i))^2) ≤
          planarTestForm (planarWellSum u) f := by
  obtain ⟨γ, hγ, hsmall, hgap⟩ := manufacturedPlanarWell_translated_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun m D η hD hη u hsep f hf hc => ?_⟩
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  have h := planarWellSum_projection_lower hsmall hgap hD u hsep f hf hc
  have hs : (∑ i, (∫ x, (planarSitePartition D u (some i) x*f x)*
      normalizedPlanarMode (x-u i))^2) ≤
      (1+η)*(∑ i, (∫ x, f x*normalizedPlanarMode (x-u i))^2) +
        (1+η⁻¹)*m*(∫ x, f x^2)*(planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))) := by
    calc
      _ ≤ ∑ i, ((1+η)*(∫ x, f x*normalizedPlanarMode (x-u i))^2 +
          (1+η⁻¹)*(∫ x, f x^2)*(planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)))) :=
        Finset.sum_le_sum (fun i _ => planarSiteCutoff_pair_bound (by linarith) hη (u i) f hL2)
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hm := mul_le_mul_of_nonneg_left hs hγ.le
  nlinarith

end ContinuumCoulomb

end

end OAI
