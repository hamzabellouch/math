import OAI.Analysis.RCDHeat.ExistingAnalytic
import OAI.Geometry.RCD.Coordinates.EuclideanWeakHarmonicRegularity

namespace OAI

/-! # Compact Sobolev tests detect the order of continuous functions

Radial Lipschitz cutoffs suffice. Full support turns a positive value
into a strictly positive integral against one of these actual tests.
-/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
  (Q : QuadraticCheegerEnergy μ)

theorem continuous_nonpos_of_sobolev_tests {Ω s : Set X} (hΩ : IsOpen Ω) (hΩs : Ω ⊆ s)
    {f : X → ℝ} (hf : ContinuousOn f Ω)
    (htest : ∀ φ : SobolevSpace μ Q,
      (∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q φ x = 0) →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ Q φ x) →
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ 1) →
      (∫ x in s, SobolevSpace.toLp μ Q φ x*f x ∂μ) ≤ 0) :
    ∀ x ∈ Ω, f x ≤ 0 := by
  intro x hx
  by_contra hn
  have hp : 0 < f x := lt_of_not_ge hn
  have he : ∀ᶠ y in 𝓝 x, y ∈ Ω ∧ 0 < f y :=
    Filter.Eventually.and (hΩ.mem_nhds hx) ((hf.continuousAt (hΩ.mem_nhds hx)).eventually
      (eventually_gt_nhds hp))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  let r := δ/4
  have hr : 0 < r := by dsimp only [r]; positivity
  let χ := radialCutoff x r
  have hχc : HasCompactSupport χ := radialCutoff_hasCompactSupport x hr
  have hχL := radialCutoff_lipschitz x hr
  have hχs : tsupport χ ⊆ closedBall x (2*r) := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    by_contra hnot
    apply hy
    exact radialCutoff_eq_zero x hr
      (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hnot))
  have hχδ : tsupport χ ⊆ ball x δ :=
    hχs.trans (closedBall_subset_ball (by dsimp only [r]; linarith))
  have hχΩ : tsupport χ ⊆ Ω := fun y hy => (hball (hχδ hy)).1
  have hχ0 (y : X) : 0 ≤ χ y := (radialCutoff_bounds x r y).1
  have hχ1 (y : X) : χ y ≤ 1 := (radialCutoff_bounds x r y).2
  let φ := radialSobolevCutoff μ Q x hr
  have hφ : SobolevSpace.toLp μ Q φ =ᵐ[μ] χ := radialSobolevCutoff_coe μ Q x hr
  have hzero (y : X) (hy : y ∉ Ω) : χ y = 0 := by
    by_contra hne
    exact hy (hχΩ (subset_tsupport χ hne))
  have hφs : ∀ᵐ y ∂μ, y ∉ Ω → SobolevSpace.toLp μ Q φ y = 0 := by
    filter_upwards [hφ] with y hy hnot
    rw [hy,hzero y hnot]
  have hφ0 : ∀ᵐ y ∂μ, 0 ≤ SobolevSpace.toLp μ Q φ y :=
    hφ.mono fun y hy => hy.symm ▸ hχ0 y
  have hφ1 : ∀ᵐ y ∂μ, |SobolevSpace.toLp μ Q φ y| ≤ 1 := by
    filter_upwards [hφ] with y hy
    rw [hy,abs_of_nonneg (hχ0 y)]
    exact hχ1 y
  have hc : Continuous (fun y => χ y*f y) :=
    continuous_mul_of_tsupport_subset hΩ hf hχL.continuous hχΩ
  have hnonneg (y : X) : 0 ≤ χ y*f y := by
    by_cases hy : χ y = 0
    · rw [hy,zero_mul]
    · exact mul_nonneg (hχ0 y) (hball (hχδ (subset_tsupport χ hy))).2.le
  have hne : χ x*f x ≠ 0 := by
    have hxx : χ x = 1 := radialCutoff_eq_one x hr (by simp; exact hr.le)
    rw [hxx,one_mul]
    exact hp.ne'
  have hpos := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := μ) hχc.mul_right hnonneg hne
  have heq : (∫ y in s, SobolevSpace.toLp μ Q φ y*f y ∂μ) = ∫ y, χ y*f y ∂μ := by
    calc
      _ = ∫ y in s, χ y*f y ∂μ := integral_congr_ae (ae_restrict_of_ae (hφ.mul (EventuallyEq.refl _ _)))
      _ = _ := setIntegral_eq_integral_of_ae_compl_eq_zero (Eventually.of_forall fun y hy => by
        have hz : χ y = 0 := hzero y (fun hyΩ => hy (hΩs hyΩ))
        rw [hz,zero_mul])
  have hle := htest φ hφs hφ0 hφ1
  rw [heq] at hle
  exact (not_lt_of_ge hle) hpos

end RegularPointCoordinates

end

end OAI
