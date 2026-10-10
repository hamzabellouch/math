import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellLocalization
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarTranslatedGap
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarCutoffTail

namespace OAI

/-! The actual planar multiwell form has a fixed excitation gap away from
the span of the translated manufactured modes, up to explicit inverse-square
localization and exponential tail errors. No multiwell spectral input is used. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planar_partition_mass {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, Continuous (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (f : PlanarPosition → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∑ i, ∫ x, (θ i x * f x)^2) = ∫ x, f x^2 := by
  have hi (i : ι) : Integrable (fun x => (θ i x * f x)^2) := by
    have hm : HasCompactSupport (fun x => θ i x * f x) := hc.mul_left
    have hs : HasCompactSupport (fun x => (θ i x * f x)^2) :=
      hm.comp_left (g := fun t : ℝ => t^2) (by norm_num)
    exact (((hθ i).mul hf).pow 2).integrable_of_hasCompactSupport hs
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [] with x
  calc
    (∑ i, (θ i x * f x)^2) = (∑ i, θ i x^2) * f x^2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hpart x, one_mul]

theorem planar_free_form_nonnegative (f : PlanarPosition → ℝ) :
    0 ≤ planarTestForm (fun _ => 0) f := by
  unfold planarTestForm
  simp only [zero_mul, integral_zero, add_zero]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun a _ => integral_nonneg (fun x => sq_nonneg _))

theorem planarWellSum_projection_lower {γ : ℝ} (hsmall : γ ≤ 1/4)
    (hgap : ∀ (u : PlanarPosition) (f : PlanarPosition → ℝ),
      ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2 : ℝ)+γ) * (∫ x, f x^2) - γ * (∫ x, f x * normalizedPlanarMode (x-u))^2 ≤
        planarTestForm (fun x => manufacturedPlanarWell (x-u)) f)
    {m : ℕ} {D : ℝ} (hD : 8 ≤ D) (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : PlanarPosition → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ((-1/2 : ℝ)+γ) * (∫ x, f x^2) -
      γ * (∑ i, (∫ x, (planarSitePartition D u (some i) x * f x) * normalizedPlanarMode (x-u i))^2) -
      planarSiteDerivativeBound D ^ 2 * (∫ x, f x^2) ≤ planarTestForm (planarWellSum u) f := by
  have hsite (i : Fin m) := hgap (u i) (fun x => planarSitePartition D u (some i) x * f x)
    ((planarSitePartition_C1 D u (some i)).mul hf)
    (show HasCompactSupport (fun x => planarSitePartition D u (some i) x * f x) from hc.mul_left)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hsite i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have he : ((-1/2 : ℝ)+γ) * (∫ x, (planarSitePartition D u none x * f x)^2) ≤
      planarTestForm (fun _ => 0) (fun x => planarSitePartition D u none x * f x) := by
    have hneg : (-1/2 : ℝ)+γ ≤ 0 := by linarith
    exact (mul_nonpos_of_nonpos_of_nonneg hneg (integral_nonneg (fun x => sq_nonneg _))).trans
      (planar_free_form_nonnegative _)
  have hm := planar_partition_mass (planarSitePartition D u)
    (fun i => (planarSitePartition_C1 D u i).continuous)
    (planarSitePartition_square_sum (by linarith : 0 < D) u hsep) f hf.continuous hc
  rw [Fintype.sum_option] at hm
  have hl := planarWellSum_localization_lower hD u hsep f hf hc
  calc
    _ = (((-1/2 : ℝ)+γ) * (∫ x, (planarSitePartition D u none x * f x)^2) +
        (((-1/2 : ℝ)+γ) * (∑ i, ∫ x, (planarSitePartition D u (some i) x * f x)^2) -
          γ * (∑ i, (∫ x, (planarSitePartition D u (some i) x * f x) * normalizedPlanarMode (x-u i))^2))) -
        planarSiteDerivativeBound D^2 * (∫ x, f x^2) := by rw [← hm]; ring
    _ ≤ _ := (sub_le_sub_right (add_le_add he hs) _).trans hl

theorem planarSiteCutoff_pair_of_orthogonal {D : ℝ} (hD : 0 < D) (u : PlanarPosition)
    (f : PlanarPosition → ℝ) (hL2 : MemLp f 2)
    (ho : (∫ x, f x * normalizedPlanarMode (x-u)) = 0) :
    (∫ x, (Real.sin (planarSiteAngle D u x) * f x) * normalizedPlanarMode (x-u))^2 ≤
      (∫ x, f x^2) * (planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8))) := by
  have hmode := normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u)
  have hi₀ : Integrable (fun x => f x * normalizedPlanarMode (x-u)) :=
    hL2.integrable_mul hmode
  have hi₁ : Integrable (fun x => f x * planarSiteCutoffError D u x) :=
    hL2.integrable_mul (planarSiteCutoffError_memLp D u)
  have hp : (∫ x, (Real.sin (planarSiteAngle D u x) * f x) * normalizedPlanarMode (x-u)) =
      ∫ x, f x * planarSiteCutoffError D u x := by
    calc
      _ = (∫ x, f x * normalizedPlanarMode (x-u)) + (∫ x, f x * planarSiteCutoffError D u x) := by
        rw [← integral_add hi₀ hi₁]
        apply integral_congr_ae
        filter_upwards [] with x
        unfold planarSiteCutoffError
        ring
      _ = _ := by rw [ho, zero_add]
  rw [hp]
  exact (planar_l2_pair_sq_le f (planarSiteCutoffError D u) hL2
    (planarSiteCutoffError_memLp D u)).trans
      (mul_le_mul_of_nonneg_left (planarSiteCutoffError_integral_bound hD u)
        (integral_nonneg (fun x => sq_nonneg _)))

/-- Quantitative actual test-domain multiwell complement bound. The only
conditional input is the cited isolated planar gap; every localization and
cutoff loss in this formula has been proved for the manufactured functions. -/
theorem planarWellSum_test_complement_bound
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D : ℝ), 8 ≤ D →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      ∀ f : PlanarPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      (∀ i, (∫ x, f x * normalizedPlanarMode (x-u i)) = 0) →
      ((-1/2 : ℝ)+γ - planarSiteDerivativeBound D^2 -
        γ * m * planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8))) * (∫ x, f x^2) ≤
          planarTestForm (planarWellSum u) f := by
  obtain ⟨γ, hγ, hsmall, hgap⟩ := manufacturedPlanarWell_translated_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun m D hD u hsep f hf hc ho => ?_⟩
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  have hp := planarWellSum_projection_lower hsmall hgap hD u hsep f hf hc
  have hs : (∑ i : Fin m,
      (∫ x, (planarSitePartition D u (some i) x * f x) * normalizedPlanarMode (x-u i))^2) ≤
      m * (∫ x, f x^2) * (planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8))) := by
    calc
      _ ≤ ∑ i : Fin m, (∫ x, f x^2) * (planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8))) :=
        Finset.sum_le_sum (fun i _ => planarSiteCutoff_pair_of_orthogonal
          (by linarith : 0 < D) (u i) f hL2 (ho i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hγs := mul_le_mul_of_nonneg_left hs hγ.le
  calc
    _ = ((-1/2 : ℝ)+γ) * (∫ x, f x^2) -
        γ * (m * (∫ x, f x^2) * (planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8)))) -
        planarSiteDerivativeBound D^2 * (∫ x, f x^2) := by ring
    _ ≤ _ := (sub_le_sub_right (sub_le_sub_left hγs _) _).trans hp

end ContinuumCoulomb

end

end OAI
