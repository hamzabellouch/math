import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.UniformHeatMassTail

namespace OAI

/-! # Uniformly small heat mass lost by an interior cutoff -/

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) [μ.Regular]
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- A cutoff equal to one on a ball loses no more mass than the heat
kernel places outside that ball. -/
theorem cutoff_heat_mass_error_le_outside {χ : X → ℝ}
    (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
    (hχrange : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (p : X) {t R : ℝ} (ht : 0 < t)
    (hχone : ∀ y ∈ ball p R, χ y = 1) :
    |(∫ y, χ y * ker t p y ∂μ) - 1| ≤ ∫ y in (ball p R)ᶜ, ker t p y ∂μ := by
  have hi : Integrable (fun y => χ y * ker t p y) μ :=
    (hχ.mul (hk.continuous_right t ht p)).integrable_of_hasCompactSupport hsχ.mul_right
  have hp := hk.integrable t ht p
  have hm : (∫ y, χ y * ker t p y ∂μ) ≤ 1 := by
    rw [← hk.mass_one t ht p]
    exact integral_mono_ae hi hp (Eventually.of_forall fun y =>
      mul_le_of_le_one_left (hk.nonneg t ht p y) (hχrange y).2)
  let f := fun y => ker t p y - χ y * ker t p y
  have hf : Integrable f μ := hp.sub hi
  have heq : |(∫ y, χ y * ker t p y ∂μ) - 1| = ∫ y, f y ∂μ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hm)]
    dsimp [f]
    rw [integral_sub hp hi, hk.mass_one t ht p]
    ring
  have hzero : ∀ y ∉ (ball p R)ᶜ, f y = 0 := by
    intro y hy
    have hymem : y ∈ ball p R := by simpa only [mem_compl_iff, not_not] using hy
    simp only [f, hχone y hymem, one_mul, sub_self]
  calc
    _ = ∫ y, f y ∂μ := heq
    _ = ∫ y in (ball p R)ᶜ, f y ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ _ := integral_mono_ae hf.integrableOn hp.integrableOn (Eventually.of_forall fun y => by
      dsimp [f]
      nlinarith [mul_nonneg (hχrange y).1 (hk.nonneg t ht p y)])

include hk in
/-- The missing mass tends uniformly to zero when the cutoff has more
and more dyadic room around its pole. -/
theorem missing_heat_mass_uniformly_small (m : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m a))
    (hfinite : ∀ x r, μ (ball x r) ≠ ∞)
    (hpos : ∀ x r, 0 < r → 0 < μ.real (ball x r))
    (hg : HasCoordinateHeatBounds μ ker) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ M, N ≤ M → ∀ p r R, 0 < r → r ≤ 1 → 2 ^ M * r ≤ R →
      ∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ →
        (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) → (∀ y ∈ ball p R, χ y = 1) →
          |(∫ y, χ y * ker (r ^ 2) p y ∂μ) - 1| < η := by
  obtain ⟨C, _hC, htail⟩ := exists_uniform_heat_mass_tail μ hQ hk m ha hBG hfinite hpos hg
  have ht : Tendsto (fun N : ℕ => C * ∑' j, gaussianMassEnvelope m a (j + N))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_sum_nat_add (gaussianMassEnvelope m a)).const_mul C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_lt_const hη)
  refine ⟨N, fun M hNM p r R hr hr1 hR χ hχ hsχ hχrange hχone => ?_⟩
  have he := cutoff_heat_mass_error_le_outside μ hQ hk hχ hsχ hχrange p
    (sq_pos_of_pos hr) hχone
  have hsub : (ball p R)ᶜ ⊆ (ball p (2 ^ M * r))ᶜ :=
    compl_subset_compl.mpr (ball_subset_ball hR)
  have hmono := setIntegral_mono_set (hk.integrable _ (sq_pos_of_pos hr) p).integrableOn
    (Eventually.of_forall fun y => hk.nonneg _ (sq_pos_of_pos hr) p y)
    (Eventually.of_forall fun _ hy => hsub hy)
  exact (he.trans (hmono.trans (htail p r hr hr1 M))).trans_lt
    (hN (M + 1) (hNM.trans (Nat.le_succ M)))

end RegularPointCoordinates

end

end OAI
