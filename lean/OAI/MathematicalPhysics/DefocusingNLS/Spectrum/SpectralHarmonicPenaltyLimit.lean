import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicPenalty
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPressureConvergence

namespace OAI

/-! The weighted penalty estimate enforces the same unweighted core constraint. -/

open MeasureTheory InnerProductSpace Filter Topology Set
namespace DefocusingNLS

theorem spectralWeightedPressure_dominates (R : ℝ) (w : SpectralHarmonicWeight R)
    (c : ℝ) (hw : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (u : SpectralRadialL2 R) :
    c*inner ℝ (spectralPressureOperator R p hpm hpb u) u ≤
      inner ℝ (spectralWeightedPressure R w p hpm hpb u) u := by
  have he : 0 ≤ inner ℝ (spectralWeightedPressure R w p hpm hpb u-
      c • spectralPressureOperator R p hpm hpb u) u := by
    change 0 ≤ ∫ r, inner ℝ ((spectralWeightedPressure R w p hpm hpb u-
      c • spectralPressureOperator R p hpm hpb u : SpectralRadialL2 R) r) (u r)
        ∂radialPressureMeasure R
    apply integral_nonneg_of_ae
    have hwa := spectralL2Weight_ae (radialPressureMeasure R) (fun r => w.density r*p r)
      (w.radial_measurable.mul hpm) w.bound (weightedPressure_bound R w p hpb) u
    filter_upwards [hwa,spectralPressureProduct_ae R p hpm hpb u,
      Lp.coeFn_sub (spectralWeightedPressure R w p hpm hpb u)
        (c • spectralPressureOperator R p hpm hpb u),
      Lp.coeFn_smul c (spectralPressureOperator R p hpm hpb u),hw,hpn]
      with r hwr hpr hsub hsm hlow hp0
    change spectralWeightedPressure R w p hpm hpb u r=(w.density r*p r) • u r at hwr
    change spectralPressureOperator R p hpm hpb u r=p r • u r at hpr
    rw [hsub,Pi.sub_apply,hsm,Pi.smul_apply,hwr,hpr,inner_sub_left,
      real_inner_smul_left,real_inner_smul_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    simp only [Pi.zero_apply]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hlow) hp0) (sq_nonneg ‖u r‖)]
  rw [inner_sub_left,real_inner_smul_left] at he
  linarith

theorem spectralHarmonicPenaltyInverse_unweightedEnergy (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (a : ℝ) (ha : 0 < a)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) :
    let u := spectralHarmonicFirstValue ell R
      (spectralHarmonicPenaltyInverse ell R w c hc hcr hca p hpm hpb hpn a ha F)
    0 ≤ (∫ r, p r*‖u r‖^2 ∂radialPressureMeasure R) ∧
      (∫ r, p r*‖u r‖^2 ∂radialPressureMeasure R) ≤ a*‖F‖^2/c^2 := by
  intro u
  have hdom := spectralWeightedPressure_dominates R w c hcr p hpm hpb hpn u
  rw [spectralPressureOperator_quadratic,spectralWeightedPressure,spectralL2Multiplier_quadratic] at hdom
  have he := spectralHarmonicPenaltyInverse_energy ell R w c hc hcr hca p hpm hpb hpn a ha F
  change (∫ r, w.density r*p r*‖u r‖^2 ∂radialPressureMeasure R) ≤ _ at he
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hpn] with r hr
    exact mul_nonneg hr (sq_nonneg _)
  · apply (le_div_iff₀ (sq_pos_of_pos hc)).2
    have hm := mul_le_mul_of_nonneg_left (hdom.trans he) hc.le
    have heq : c*(a*‖F‖^2/c)=a*‖F‖^2 := by field_simp
    rw [heq] at hm
    nlinarith

theorem spectralHarmonicPenaltyInverse_core_limit (ell : ℕ) (R l b : ℝ) (hb : 0 < b)
    (w : ℕ → SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, c ≤ (w n).density r)
    (hca : ∀ n, ∀ᵐ r ∂spectralAngularMeasure R, c ≤ (w n).density r)
    (p : ℕ → ℝ → ℝ) (hpm : ∀ n, AEStronglyMeasurable (p n) (radialPressureMeasure R))
    (hpb : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖p n r‖ ≤ 1)
    (hpn : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p n r)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0))
    (F : ℕ → StrongDual ℝ (SpectralHarmonicPair ell R)) (M : ℝ) (hF : ∀ n, ‖F n‖ ≤ M)
    (hweak : ∀ φ : ℝ → ℝ, Integrable φ (radialPressureMeasure R) →
      Tendsto (fun n => ∫ r, p n r*φ r ∂radialPressureMeasure R) atTop
        (𝓝 (∫ r, (Iic l).indicator (fun _ : ℝ => b) r*φ r ∂radialPressureMeasure R)))
    (v : SpectralHarmonicPair ell R)
    (hvol : Tendsto (fun n => spectralHarmonicFirstValue ell R
      (spectralHarmonicPenaltyInverse ell R (w n) c hc (hcr n) (hca n)
        (p n) (hpm n) (hpb n) (hpn n) (a n) (ha n) (F n))) atTop
          (𝓝 (spectralHarmonicFirstValue ell R v))) :
    v ∈ spectralHarmonicCoreSubspace ell R l := by
  apply (spectralHarmonicCore_mem ell R l v).2
  apply spectral_pressure_core_constraint R l b hb p hpm hpb hweak _ _ hvol a ha0 (M^2/c^2)
  intro n
  have he := spectralHarmonicPenaltyInverse_unweightedEnergy ell R (w n) c hc (hcr n) (hca n)
    (p n) (hpm n) (hpb n) (hpn n) (a n) (ha n) (F n)
  refine ⟨he.1,he.2.trans ?_⟩
  have hM : 0 ≤ M := (norm_nonneg (F n)).trans (hF n)
  have hsq := (sq_le_sq₀ (norm_nonneg (F n)) hM).2 (hF n)
  calc
    a n*‖F n‖^2/c^2 ≤ a n*M^2/c^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (ha n).le) (sq_nonneg c)
    _ = M^2/c^2*a n := by ring

end DefocusingNLS

end OAI
