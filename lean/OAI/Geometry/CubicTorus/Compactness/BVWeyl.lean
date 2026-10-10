import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVBallProbability
import OAI.Geometry.CubicTorus.Regularity.BVNormalTiltMeasure

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

def planarMollifier (i : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((i : ℝ) + 1)
  rOut := 2 / ((i : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

lemma planarMollifier_tendsto : Tendsto (fun i ↦ (planarMollifier i).rOut) atTop (𝓝 0) := by
  simpa only [planarMollifier, mul_one, mul_div, mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma planarMollifier_ratio (i : ℕ) :
    (planarMollifier i).rOut ≤ 2 * (planarMollifier i).rIn := by
  dsimp only [planarMollifier]
  rw [mul_div, mul_one]

theorem weak_harmonic_radial_reproduction {f k : ℂ → ℝ} {κ : ℝ → ℝ}
    {Ω : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball c (4 * R) ⊆ Ω) (hf : LocallyIntegrable f)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, f y * Δ φ y) = 0)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hks : HasCompactSupport k)
    (hrad : ∀ z, k z = κ ‖z‖) (hc : Continuous κ)
    (hκ : ∀ r, R < r → κ r = 0) (hi : (∫ z, k z) = 1) :
    f =ᵐ[volume.restrict (Metric.ball c R)] f ⋆[ContinuousLinearMap.mul ℝ ℝ] k := by
  let p (i : ℕ) : ℂ → ℝ := (planarMollifier i).normed volume
  let u : ℂ → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ] k
  have hu : Continuous u := hks.continuous_convolution_right _ hf hk.continuous
  have hp (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (p i) := (planarMollifier i).contDiff_normed
  have hps (i : ℕ) : HasCompactSupport (p i) := (planarMollifier i).hasCompactSupport_normed
  have hsmall : ∀ᶠ i in atTop, (planarMollifier i).rOut < R :=
    planarMollifier_tendsto.eventually (gt_mem_nhds hR)
  have hharm (i : ℕ) (hiR : (planarMollifier i).rOut < R) :
      InnerProductSpace.HarmonicOnNhd (f ⋆[ContinuousLinearMap.mul ℝ ℝ] p i)
        (Metric.ball c (3 * R)) := by
    apply weak_harmonic_convolution hf hweak (hp i) (hps i) Metric.isOpen_ball
    intro x hx
    apply Subset.trans _ hball
    apply reflected_tsupport_subset_ball
      (le_of_eq ((planarMollifier i).tsupport_normed_eq (μ := volume)))
    have hx' : dist x c < 3 * R := hx
    linarith
  have he (x : ℂ) (hx : x ∈ Metric.ball c R) :
      ∀ᶠ i in atTop, (u ⋆[ContinuousLinearMap.mul ℝ ℝ] p i) x =
        (f ⋆[ContinuousLinearMap.mul ℝ ℝ] p i) x := by
    filter_upwards [hsmall] with i hiR
    rw [← compact_convolutions_commute hf (hp i).continuous (hps i) hk.continuous hks]
    apply harmonic_radial_convolution
      ((hps i).continuous_convolution_right _ hf (hp i).continuous) hrad hc hκ hi
    apply (hharm i hiR).mono
    intro y hy
    have hy' : dist y x ≤ R := hy
    have hx' : dist x c < R := hx
    change dist y c < 3 * R
    have ht := dist_triangle y x c
    linarith
  have hfa := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    planarMollifier_tendsto (Eventually.of_forall planarMollifier_ratio) hf
  filter_upwards [ae_restrict_of_ae hfa, ae_restrict_mem measurableSet_ball] with x hx hxball
  have hua := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) planarMollifier_tendsto hu x
  change Tendsto (fun i ↦ (p i ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x) atTop (𝓝 (f x)) at hx
  change Tendsto (fun i ↦ (p i ⋆[ContinuousLinearMap.mul ℝ ℝ] u) x) atTop (𝓝 (u x)) at hua
  simp_rw [real_convolution_comm (p _) f] at hx
  simp_rw [real_convolution_comm (p _) u] at hua
  exact tendsto_nhds_unique hx (hua.congr' (he x hxball))

theorem weak_harmonic_local_representative {f : ℂ → ℝ} {Ω : Set ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hball : Metric.ball c (4 * R) ⊆ Ω) (hf : LocallyIntegrable f)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, f y * Δ φ y) = 0) :
    ∃ u : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧
      InnerProductSpace.HarmonicOnNhd u (Metric.ball c R) ∧
      f =ᵐ[volume.restrict (Metric.ball c R)] u := by
  obtain ⟨k, κ, hk, hks, hrad, hc, hκ, hsupport, hi⟩ := exists_radial_smoothing_kernel hR
  refine ⟨f ⋆[ContinuousLinearMap.mul ℝ ℝ] k,
    hks.contDiff_convolution_right _ hf hk, ?_,
    weak_harmonic_radial_reproduction hR hball hf hweak hk hks hrad hc hκ hi⟩
  apply weak_harmonic_convolution hf hweak hk hks Metric.isOpen_ball
  intro x hx
  apply Subset.trans _ hball
  apply reflected_tsupport_subset_ball hsupport
  have hx' : dist x c < R := hx
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma second_deriv_convolution_le {f k : X → ℝ} (hf : Integrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ k) x‖ ≤ C) (x : X) :
    ‖fderiv ℝ (fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k)) x‖ ≤
      C * ∫ y, ‖f y‖ ∂μ := by
  let u : X → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hs.contDiff_convolution_right _ hf.locallyIntegrable hk
  have hm : 0 ≤ ∫ y, ‖f y‖ ∂μ := integral_nonneg (fun _ ↦ norm_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hm)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ fderiv ℝ k z w) :=
    (hk.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun z ↦ fderiv ℝ u z w) =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun z ↦ fderiv ℝ k z w) :=
    funext (fun z ↦ fderiv_compact_convolution hf.locallyIntegrable hk hs z w)
  rw [← fderiv_fderiv_apply hu, he,
    fderiv_compact_convolution hf.locallyIntegrable hd (hs.fderiv_apply ℝ w), convolution_mul]
  have hi : Integrable (fun t ↦ (C * ‖v‖ * ‖w‖) * ‖f t‖) μ := hf.norm.const_mul _
  calc
    _ ≤ ∫ t, (C * ‖v‖ * ‖w‖) * ‖f t‖ ∂μ := by
      apply norm_integral_le_of_norm_le hi
      exact Eventually.of_forall fun t ↦ by
        rw [norm_mul, fderiv_fderiv_apply hk]
        have hb' : ‖(fderiv ℝ (fderiv ℝ k) (x - t) v) w‖ ≤ C * ‖v‖ * ‖w‖ := by
          calc
            _ ≤ ‖fderiv ℝ (fderiv ℝ k) (x - t) v‖ * ‖w‖ :=
              (fderiv ℝ (fderiv ℝ k) (x - t) v).le_opNorm w
            _ ≤ (‖fderiv ℝ (fderiv ℝ k) (x - t)‖ * ‖v‖) * ‖w‖ := by
              gcongr
              exact (fderiv ℝ (fderiv ℝ k) (x - t)).le_opNorm v
            _ ≤ _ := by gcongr; exact hb (x - t)
        calc
          _ ≤ ‖f t‖ * (C * ‖v‖ * ‖w‖) := mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
          _ = _ := mul_comm _ _
    _ = _ := by rw [integral_const_mul]; ring

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_compact_norm_bound {Y : Type*} [NormedAddCommGroup Y]
    {g : X → Y} (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hs.norm
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact (hC (mem_range_self x)).trans (le_max_left _ _)

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma smooth_compact_hessian_bound {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ k) x‖ ≤ C := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ k) := hk.fderiv_right (by simp)
  have hd₂ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ k)) := hd.fderiv_right (by simp)
  exact continuous_compact_norm_bound hd₂.continuous ((hs.fderiv ℝ).fderiv ℝ)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma quadratic_taylor_bound {u : X → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M) (x : X) :
    ‖u x - u 0 - fderiv ℝ u 0 x‖ ≤ M * ‖x‖ ^ 2 := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hl (y : X) : ‖fderiv ℝ u y - fderiv ℝ u 0‖ ≤ M * ‖y‖ := by
    simpa using (convex_univ : Convex ℝ (Set.univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hd.differentiable (by simp) |>.differentiableAt)
      (fun z _ ↦ hb z) (mem_univ (0 : X)) (mem_univ y)
  let v : X → ℝ := fun y ↦ u y - u 0 - fderiv ℝ u 0 y
  have hv (y : X) : HasFDerivAt v (fderiv ℝ u y - fderiv ℝ u 0) y := by
    exact ((hu.differentiable (by simp)).differentiableAt.hasFDerivAt.sub_const
      (u 0)).sub ((fderiv ℝ u 0).hasFDerivAt)
  have he := (convex_closedBall (0 : X) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ (hv y).differentiableAt)
    (C := M * ‖x‖)
    (fun y hy ↦ by
      rw [(hv y).fderiv]
      exact (hl y).trans (mul_le_mul_of_nonneg_left (by simpa using hy) hM))
    (Metric.mem_closedBall_self (norm_nonneg x))
    (by simp : x ∈ Metric.closedBall (0 : X) ‖x‖)
  simpa [v, pow_two, mul_assoc] using he

variable [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.IsAddHaarMeasure]

lemma compact_convolution_affine_approximation {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : X → ℝ, Integrable f μ → ∀ x : X,
      let u := f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k
      ‖u x - u 0 - fderiv ℝ u 0 x‖ ≤ C * (∫ y, ‖f y‖ ∂μ) * ‖x‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := smooth_compact_hessian_bound hk hs
  refine ⟨C, hC, fun f hf x ↦ ?_⟩
  apply quadratic_taylor_bound (hs.contDiff_convolution_right _ hf.locallyIntegrable hk)
  · exact mul_nonneg hC.le (integral_nonneg fun _ ↦ norm_nonneg _)
  · exact second_deriv_convolution_le hf hk hs hC.le hbound

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

theorem weak_harmonic_affine_approximation {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℝ, Integrable f →
      (∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 (4 * R) → (∫ y, f y * Δ φ y) = 0) →
      ∃ b : ℝ, ∃ l : ℂ →L[ℝ] ℝ,
        ∀ᵐ x ∂volume.restrict (Metric.ball (0 : ℂ) R),
          ‖f x - b - l x‖ ≤ C * (∫ y, ‖f y‖) * ‖x‖ ^ 2 := by
  obtain ⟨k, κ, hk, hks, hrad, hc, hκ, _, hi⟩ := exists_radial_smoothing_kernel hR
  obtain ⟨C, hC, hbound⟩ := compact_convolution_affine_approximation (μ := volume) hk hks
  refine ⟨C, hC, fun f hf hw ↦ ?_⟩
  let u := f ⋆[ContinuousLinearMap.mul ℝ ℝ] k
  refine ⟨u 0, fderiv ℝ u 0, ?_⟩
  have he := weak_harmonic_radial_reproduction hR (Subset.refl _)
    hf.locallyIntegrable hw hk hks hrad hc hκ hi
  filter_upwards [he] with x hx
  rw [hx]
  exact hbound f hf x

lemma planar_affine_error_energy {f : ℂ → ℝ} {b A R ρ : ℝ}
    {l : ℂ →L[ℝ] ℝ} (hf : AEStronglyMeasurable f)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (hb : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : ℂ) R),
      ‖f x - b - l x‖ ≤ A * ‖x‖ ^ 2) :
    (∫ x in Metric.ball (0 : ℂ) ρ, (f x - b - l x) ^ 2) ≤
      Real.pi * A ^ 2 * ρ ^ 6 := by
  let ν := volume.restrict (Metric.ball (0 : ℂ) ρ)
  let : IsFiniteMeasure ν := ⟨by
    change volume.restrict (Metric.ball (0 : ℂ) ρ) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact Metric.isBounded_ball.measure_lt_top⟩
  have hs : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hρR
  have he : ∀ᵐ x ∂ν, ‖(f x - b - l x) ^ 2‖ ≤ A ^ 2 * ρ ^ 4 := by
    filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) hb,
      ae_restrict_mem measurableSet_ball] with x hx hxball
    have hxρ : ‖x‖ ≤ ρ := by simpa using (show dist x 0 ≤ ρ from le_of_lt hxball)
    calc
      _ = ‖f x - b - l x‖ ^ 2 := norm_pow _ _
      _ ≤ (A * ‖x‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
      _ ≤ (A * ρ ^ 2) ^ 2 := by gcongr
      _ = _ := by ring
  have hi : Integrable (fun x ↦ (f x - b - l x) ^ 2) ν := by
    apply (integrable_const (A ^ 2 * ρ ^ 4)).mono' _ he
    exact ((hf.mono_measure Measure.restrict_le_self).sub aestronglyMeasurable_const |>.sub
      l.continuous.aestronglyMeasurable).pow 2
  calc
    _ ≤ ∫ _ : ℂ, A ^ 2 * ρ ^ 4 ∂ν := integral_mono_ae hi (integrable_const _)
      (he.mono fun x hx ↦ (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hx))
    _ = Real.pi * A ^ 2 * ρ ^ 6 := by
      rw [integral_const]
      simp only [ν, Measure.real, Measure.restrict_apply_univ, Complex.volume_ball,
        ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ,
        smul_eq_mul]
      change ρ ^ 2 * Real.pi * (A ^ 2 * ρ ^ 4) = _
      ring

theorem weak_harmonic_height_decay {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℝ, Integrable f →
      (∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 (4 * R) → (∫ y, f y * Δ φ y) = 0) →
      ∃ b : ℝ, ∃ l : ℂ →L[ℝ] ℝ, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ R →
        (∫ x in Metric.ball (0 : ℂ) ρ, (f x - b - l x) ^ 2) ≤
          C * (∫ y, ‖f y‖) ^ 2 * ρ ^ 6 := by
  obtain ⟨C, hC, hb⟩ := weak_harmonic_affine_approximation hR
  refine ⟨Real.pi * C ^ 2, by positivity, fun f hf hw ↦ ?_⟩
  obtain ⟨b, l, hbound⟩ := hb f hf hw
  refine ⟨b, l, fun ρ hρ hρR ↦ ?_⟩
  have he := planar_affine_error_energy hf.aestronglyMeasurable
    (mul_nonneg hC.le (integral_nonneg fun _ ↦ norm_nonneg _)) hρ hρR hbound
  convert he using 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma weak_harmonic_comp_isometry {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (L : X ≃ₗᵢ[ℝ] Y) {f : Y → ℝ} {R : ℝ}
    (hf : ∀ φ : Y → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R → (∫ y, f y * Δ φ y) = 0) :
    ∀ φ : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R → (∫ y, (f ∘ L) y * Δ φ y) = 0 := by
  intro φ hφ hs hb
  have hsupport : tsupport (φ ∘ L.symm) ⊆ Metric.ball 0 R := by
    rw [show tsupport (φ ∘ L.symm) = L.symm ⁻¹' tsupport φ from
      tsupport_comp_eq_preimage φ L.symm.toHomeomorph]
    intro y hy
    have hh := hb hy
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hh
  have hh := hf (φ ∘ L.symm) (hφ.comp L.symm.contDiff)
    (hs.comp_homeomorph L.symm.toHomeomorph) hsupport
  rw [← L.measurePreserving.integral_comp L.toMeasurableEquiv.measurableEmbedding] at hh
  simpa only [Function.comp_apply, laplacian_comp_isometry L.symm hφ,
    LinearIsometryEquiv.symm_apply_apply] using hh

theorem plane_weak_harmonic_height_decay {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Plane → ℝ, Integrable f →
      (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 (4 * R) → (∫ y, f y * Δ φ y) = 0) →
      ∃ b : ℝ, ∃ l : Plane →L[ℝ] ℝ, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ R →
        (∫ x in Metric.ball (0 : Plane) ρ, (f x - b - l x) ^ 2) ≤
          C * (∫ y, ‖f y‖) ^ 2 * ρ ^ 6 := by
  let L := Complex.orthonormalBasisOneI.repr
  obtain ⟨C, hC, hb⟩ := weak_harmonic_height_decay hR
  refine ⟨C, hC, fun f hf hw ↦ ?_⟩
  obtain ⟨b, l, he⟩ := hb (f ∘ L)
    ((L.measurePreserving.integrable_comp hf.aestronglyMeasurable).mpr hf)
    (weak_harmonic_comp_isometry L hw)
  refine ⟨b, l.comp L.symm.toContinuousLinearEquiv.toContinuousLinearMap, fun ρ hρ hρR ↦ ?_⟩
  have hn : (∫ y, ‖(f ∘ L) y‖) = ∫ y, ‖f y‖ := by
    exact L.measurePreserving.integral_comp L.toMeasurableEquiv.measurableEmbedding
      (fun y : Plane ↦ ‖f y‖)
  have hmeasure : MeasurePreserving L
      (volume.restrict (Metric.ball (0 : ℂ) ρ))
      (volume.restrict (Metric.ball (0 : Plane) ρ)) := by
    simpa only [L.preimage_ball, map_zero] using
      L.measurePreserving.restrict_preimage (measurableSet_ball (x := (0 : Plane)) (ε := ρ))
  have hi := hmeasure.integral_comp L.toMeasurableEquiv.measurableEmbedding
    (fun y ↦ (f y - b - l (L.symm y)) ^ 2)
  have hh := he ρ hρ hρR
  rw [hn] at hh
  simp only [LinearIsometryEquiv.symm_apply_apply] at hi
  change (∫ x in Metric.ball (0 : ℂ) ρ, (f (L x) - b - l x) ^ 2) ≤ _ at hh
  rw [hi] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma L2_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Lp ℝ 2 μ) : ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ ↦ by simp [pow_two]

lemma L2_toLp_dist_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : MemLp f 2 μ) (u : Lp ℝ 2 μ) :
    dist (hf.toLp f) u ^ 2 = ∫ x, (f x - u x) ^ 2 ∂μ := by
  rw [dist_eq_norm, L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) u, hf.coeFn_toLp] with x hx hxf
  simp only [hx, Pi.sub_apply, hxf]

lemma integral_mul_eq_restrict_of_tsupport {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} {K : Set X} (hK : MeasurableSet K)
    (f q : X → ℝ) (hq : tsupport q ⊆ K) :
    (∫ x, f x * q x ∂μ) = ∫ x in K, f x * q x ∂μ := by
  rw [← integral_indicator hK]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      change f x * q x = 0
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hq h)), mul_zero]

theorem L2_weak_harmonic_limit {K Ω : Set Plane} (hK : IsCompact K) (hΩ : Ω ⊆ K)
    {f : ℕ → Plane → ℝ} (hf : ∀ i, MemLp (f i) 2 (volume.restrict K))
    {u : Lp ℝ 2 (volume.restrict K)}
    (hu : Tendsto (fun i ↦ (hf i).toLp (f i)) atTop (𝓝 u))
    (hw : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → Tendsto (fun i ↦ ∫ y, f i y * Δ φ y) atTop (𝓝 0)) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, K.indicator (fun x ↦ u x) y * Δ φ y) = 0 := by
  intro φ hφ hs hb
  have hlaps : HasCompactSupport (Δ φ) := hs.mono' ((subset_tsupport _).trans (laplacian_tsupport_subset hφ))
  have hlap : MemLp (Δ φ) 2 (volume.restrict K) :=
    (compact_laplacian_continuous hφ).memLp_of_hasCompactSupport hlaps
  let v := hlap.toLp (Δ φ)
  have hpair (i : ℕ) : (∫ x, ((hf i).toLp (f i)) x * v x ∂volume.restrict K) =
      ∫ x, f i x * Δ φ x := by
    rw [integral_mul_eq_restrict_of_tsupport hK.measurableSet (f i) (Δ φ)
      ((laplacian_tsupport_subset hφ).trans (hb.trans hΩ))]
    apply integral_congr_ae
    filter_upwards [(hf i).coeFn_toLp, hlap.coeFn_toLp] with x hx hv
    rw [hx, hv]
  have hz := L2_pairing_limit_zero hu v (by simpa only [hpair] using hw φ hφ hs hb)
  calc
    _ = ∫ x in K, u x * Δ φ x := by
      rw [← integral_indicator hK.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by simp only [indicator_mul_left]
    _ = ∫ x, u x * v x ∂volume.restrict K := by
      apply integral_congr_ae
      filter_upwards [hlap.coeFn_toLp] with x hx
      rw [hx]
    _ = 0 := hz

lemma L2_zero_extension_bounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} (hK : MeasurableSet K) (hfin : μ K ≠ ⊤)
    (u : Lp ℝ 2 (μ.restrict K)) :
    Integrable (K.indicator (fun x ↦ u x)) μ ∧
      (∫ x, ‖K.indicator (fun y ↦ u y) x‖ ∂μ) ^ 2 ≤ μ.real K * ‖u‖ ^ 2 := by
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hfin
  have hi : Integrable (fun x ↦ u x) (μ.restrict K) := MemLp.integrable (by norm_num) (Lp.memLp u)
  have hs : Integrable (fun x ↦ ‖u x‖ ^ 2) (μ.restrict K) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  refine ⟨IntegrableOn.integrable_indicator hi hK, ?_⟩
  have he : (fun x ↦ ‖K.indicator (fun y ↦ u y) x‖) = K.indicator (fun x ↦ ‖u x‖) := by
    funext x
    simp only [norm_indicator_eq_indicator_norm]
  rw [he, integral_indicator hK, L2_norm_sq_integral]
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.norm_eq_abs, sq_abs] using
    integral_square_le_mass hi.norm hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma L2_energy_triangle {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f u v : X → ℝ} (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (∫ x, (f x - v x) ^ 2 ∂μ) ≤
      2 * (∫ x, (f x - u x) ^ 2 ∂μ) + 2 * (∫ x, (u x - v x) ^ 2 ∂μ) := by
  have hfu := (memLp_two_iff_integrable_sq (hf.sub hu).aestronglyMeasurable).mp (hf.sub hu)
  have huv := (memLp_two_iff_integrable_sq (hu.sub hv).aestronglyMeasurable).mp (hu.sub hv)
  have hfv := (memLp_two_iff_integrable_sq (hf.sub hv).aestronglyMeasurable).mp (hf.sub hv)
  simp only [Pi.sub_apply] at hfu huv hfv
  calc
    _ ≤ ∫ x, 2 * (f x - u x) ^ 2 + 2 * (u x - v x) ^ 2 ∂μ :=
      integral_mono hfv ((hfu.const_mul 2).add (huv.const_mul 2))
        (fun x ↦ by nlinarith [sq_nonneg (f x - 2 * u x + v x)])
    _ = _ := by rw [integral_add (hfu.const_mul 2) (huv.const_mul 2), integral_const_mul,
      integral_const_mul]

theorem planar_H1_harmonic_approximation {R : ℝ} (hR : 0 < R)
    {K : Set Plane} (hK : IsCompact K) (hball : Metric.ball (0 : Plane) (4 * R) ⊆ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℕ → Plane → ℝ) (L : ℕ → ℝ≥0),
        (∀ i, LipschitzWith (L i) (f i)) →
        (∀ i, Integrable (fun x ↦ f i x ^ 2)) →
        (∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖ ^ 2)) →
      ∀ M D : ℝ, 0 ≤ D →
        (∀ i, (∫ x, f i x ^ 2) ≤ M) →
        (∀ i, (∫ x, ‖fderiv ℝ (f i) x‖ ^ 2) ≤ D) →
        (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball 0 (4 * R) →
          Tendsto (fun i ↦ ∫ y, f i y * Δ φ y) atTop (𝓝 0)) →
      ∃ (ψ : ℕ → ℕ) (b : ℝ) (l : Plane →L[ℝ] ℝ), StrictMono ψ ∧
        ∀ ρ ε : ℝ, 0 ≤ ρ → ρ ≤ R → 0 < ε →
          ∀ᶠ i in atTop,
            (∫ x in Metric.ball (0 : Plane) ρ, (f (ψ i) x - b - l x) ^ 2) ≤
              C * M * ρ ^ 6 + ε := by
  obtain ⟨C₀, hC₀, hdecay⟩ := plane_weak_harmonic_height_decay hR
  let vK := (volume : Measure Plane).real K
  refine ⟨2 * C₀ * (vK + 1), by dsimp [vK]; positivity, ?_⟩
  intro f L hf hfs hgrad M D hDnon hM hD hw
  obtain ⟨u, ψ, hψ, hmem, hu⟩ := restricted_H1_subsequence hK f L hf hfs hgrad hDnon hM hD
  have hMass : 0 ≤ M := (integral_nonneg (fun x ↦ sq_nonneg (f 0 x))).trans (hM 0)
  have hnorm : ‖u‖ ^ 2 ≤ M := by
    apply le_of_tendsto (hu.norm.pow 2)
    exact Eventually.of_forall fun i ↦ by
      rw [L2_norm_sq_integral]
      calc
        _ = ∫ x in K, f (ψ i) x ^ 2 := integral_congr_ae
          ((hmem (ψ i)).coeFn_toLp.mono fun x hx ↦ by rw [hx])
        _ ≤ ∫ x, f (ψ i) x ^ 2 := integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun _ ↦ sq_nonneg _) (hfs (ψ i))
        _ ≤ M := hM (ψ i)
  let U : Plane → ℝ := K.indicator (fun x ↦ u x)
  have hU := L2_zero_extension_bounds hK.measurableSet hK.measure_lt_top.ne u
  have hweak := L2_weak_harmonic_limit hK hball (fun i ↦ hmem (ψ i)) hu
    (fun φ hφ hs hb ↦ (hw φ hφ hs hb).comp hψ.tendsto_atTop)
  obtain ⟨b, l, hheight⟩ := hdecay U hU.1 hweak
  refine ⟨ψ, b, l, hψ, fun ρ ε hρ hρR hε ↦ ?_⟩
  have hρK : Metric.ball (0 : Plane) ρ ⊆ K :=
    (Metric.ball_subset_ball (by linarith : ρ ≤ 4 * R)).trans hball
  have hsmall : Tendsto (fun i ↦ ∫ x in K, (f (ψ i) x - u x) ^ 2) atTop (𝓝 0) := by
    have hh := (hu.dist (tendsto_const_nhds (x := u))).pow 2
    simpa only [dist_self, zero_pow (by norm_num : 2 ≠ 0), L2_toLp_dist_sq] using hh
  have hlimbound : (∫ x in Metric.ball (0 : Plane) ρ, (u x - b - l x) ^ 2) ≤
      C₀ * vK * M * ρ ^ 6 := by
    have he : (∫ x in Metric.ball (0 : Plane) ρ, (u x - b - l x) ^ 2) =
        ∫ x in Metric.ball (0 : Plane) ρ, (U x - b - l x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      rw [show U x = u x from indicator_of_mem (hρK hx) _]
    rw [he]
    apply (hheight ρ hρ hρR).trans
    have hh : (∫ y, ‖U y‖) ^ 2 ≤ vK * M := hU.2.trans
      (mul_le_mul_of_nonneg_left hnorm (measureReal_nonneg))
    have hmul := mul_le_mul_of_nonneg_left hh
      (mul_nonneg hC₀.le (pow_nonneg hρ 6))
    nlinarith [hmul]
  have haff : MemLp (fun x : Plane ↦ b + l x) 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq (continuous_const.add l.continuous).aestronglyMeasurable).mpr
    exact ContinuousOn.integrableOn_compact hK ((continuous_const.add l.continuous).pow 2).continuousOn
  filter_upwards [hsmall.eventually (gt_mem_nhds (half_pos hε))] with i hi
  have htri := L2_energy_triangle
    ((hmem (ψ i)).mono_measure (Measure.restrict_mono hρK le_rfl))
    ((Lp.memLp u).mono_measure (Measure.restrict_mono hρK le_rfl))
    (haff.mono_measure (Measure.restrict_mono hρK le_rfl))
  have herr : (∫ x in Metric.ball (0 : Plane) ρ, (f (ψ i) x - u x) ^ 2) < ε / 2 := by
    apply lt_of_le_of_lt _ hi
    exact integral_mono_measure (Measure.restrict_mono hρK le_rfl)
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
      ((memLp_two_iff_integrable_sq ((hmem (ψ i)).sub (Lp.memLp u)).aestronglyMeasurable).mp
        ((hmem (ψ i)).sub (Lp.memLp u)))
  simp only [sub_add_eq_sub_sub] at htri
  have hnon : 0 ≤ C₀ * M * ρ ^ 6 := by positivity
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_bounded_mul {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hA : ∀ x, |f x| ≤ A) (hB : ∀ x, |g x| ≤ B) :
    LipschitzWith (A * L + B * K) (fun x ↦ f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [he]
  have h₁ := hg.dist_le_mul x y
  have h₂ := hf.dist_le_mul x y
  simp only [Real.dist_eq] at h₁ h₂
  calc
    _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
      simpa only [abs_mul] using abs_add_le (f x * (g x - g y)) (g y * (f x - f y))
    _ ≤ (A : ℝ) * (L * dist x y) + (B : ℝ) * (K * dist x y) :=
      add_le_add (mul_le_mul (hA x) h₁ (abs_nonneg _) (NNReal.coe_nonneg _))
        (mul_le_mul (hB y) h₂ (abs_nonneg _) (NNReal.coe_nonneg _))
    _ = _ := by push_cast; ring

lemma fderiv_mul_sq_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y ↦ f y * g y) x‖ ^ 2 ≤
      2 * f x ^ 2 * ‖fderiv ℝ g x‖ ^ 2 + 2 * g x ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by
  change ‖fderiv ℝ (f * g) x‖ ^ 2 ≤ _
  rw [fderiv_mul hf hg]
  have hb := norm_add_le (f x • fderiv ℝ g x) (g x • fderiv ℝ f x)
  simp only [norm_smul, Real.norm_eq_abs] at hb
  have ha := norm_nonneg (f x • fderiv ℝ g x + g x • fderiv ℝ f x)
  nlinarith [sq_abs (f x), sq_abs (g x),
    sq_nonneg (|f x| * ‖fderiv ℝ g x‖ - |g x| * ‖fderiv ℝ f x‖)]

lemma fderiv_mul_sq_bound_of_bounds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f ζ : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (hζ : DifferentiableAt ℝ ζ x)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |ζ x| ≤ A) (hb : ‖fderiv ℝ ζ x‖ ≤ B) :
    ‖fderiv ℝ (fun y ↦ ζ y * f y) x‖ ^ 2 ≤
      2 * A ^ 2 * ‖fderiv ℝ f x‖ ^ 2 + 2 * B ^ 2 * f x ^ 2 := by
  have hp := fderiv_mul_sq_bound hζ hf
  have hz : ζ x ^ 2 ≤ A ^ 2 := by nlinarith [sq_abs (ζ x), abs_nonneg (ζ x)]
  have hd : ‖fderiv ℝ ζ x‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg (fderiv ℝ ζ x)]
  nlinarith [mul_le_mul_of_nonneg_right hz (sq_nonneg ‖fderiv ℝ f x‖),
    mul_le_mul_of_nonneg_left hd (sq_nonneg (f x))]

lemma integrable_integral_le_of_support_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S : Set X} {u q : X → ℝ}
    (hu : AEStronglyMeasurable u μ) (hq : IntegrableOn q S μ)
    (hzero : ∀ x ∉ S, u x = 0)
    (hb : ∀ᵐ x ∂μ.restrict S, |u x| ≤ q x) :
    Integrable u μ ∧ (∫ x, u x ∂μ) ≤ ∫ x in S, q x ∂μ := by
  have hi : IntegrableOn u S μ := hq.mono' hu.restrict (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨hi.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact integral_mono_ae hi hq (hb.mono fun x hx ↦ (le_abs_self (u x)).trans hx)

theorem lipschitz_cutoff_H1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    {f ζ : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hζ : ContDiff ℝ 1 ζ) (_hs : HasCompactSupport ζ)
    {S : Set X} (hS : IsCompact S) (hsub : tsupport ζ ⊆ S)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, |ζ x| ≤ A) (hb : ∀ x, ‖fderiv ℝ ζ x‖ ≤ B) :
    Integrable (fun x ↦ (ζ x * f x) ^ 2) μ ∧
    Integrable (fun x ↦ ‖fderiv ℝ (fun y ↦ ζ y * f y) x‖ ^ 2) μ ∧
    (∫ x, (ζ x * f x) ^ 2 ∂μ) ≤ A ^ 2 * ∫ x in S, f x ^ 2 ∂μ ∧
    (∫ x, ‖fderiv ℝ (fun y ↦ ζ y * f y) x‖ ^ 2 ∂μ) ≤
      2 * A ^ 2 * (∫ x in S, ‖fderiv ℝ f x‖ ^ 2 ∂μ) +
        2 * B ^ 2 * (∫ x in S, f x ^ 2 ∂μ) := by
  have hfs : IntegrableOn (fun x ↦ f x ^ 2) S μ :=
    ContinuousOn.integrableOn_compact hS (hf.continuous.pow 2).continuousOn
  let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  have hdf := lipschitz_fderiv_sq_integrable (μ := μ.restrict S) hf
  have hzero (x : X) (hx : x ∉ S) : ζ x * f x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsub h)), zero_mul]
  have hdzero (x : X) (hx : x ∉ S) : fderiv ℝ (fun y ↦ ζ y * f y) x = 0 := by
    apply fderiv_of_notMem_tsupport ℝ
    intro h
    exact hx (hsub (tsupport_mul_subset_left h))
  have hi := integrable_integral_le_of_support_bound
    (u := fun x ↦ (ζ x * f x) ^ 2) (q := fun x ↦ A ^ 2 * f x ^ 2)
    ((hζ.continuous.mul hf.continuous).pow 2).aestronglyMeasurable (hfs.const_mul (A ^ 2))
    (fun x hx ↦ by simp only [hzero x hx, zero_pow (by norm_num : 2 ≠ 0)]) (by
      apply Eventually.of_forall
      intro x
      rw [abs_of_nonneg (sq_nonneg _)]
      have hh : ζ x ^ 2 ≤ A ^ 2 := by nlinarith [ha x, sq_abs (ζ x), abs_nonneg (ζ x)]
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (f x))])
  have hid := integrable_integral_le_of_support_bound (μ := μ) (S := S)
    (u := fun x ↦ ‖fderiv ℝ (fun y ↦ ζ y * f y) x‖ ^ 2)
    (q := fun x ↦ 2 * A ^ 2 * ‖fderiv ℝ f x‖ ^ 2 + 2 * B ^ 2 * f x ^ 2)
    ((measurable_fderiv ℝ (fun y ↦ ζ y * f y)).norm.pow_const 2).aestronglyMeasurable
    (show IntegrableOn (fun x ↦ 2 * A ^ 2 * ‖fderiv ℝ f x‖ ^ 2 + 2 * B ^ 2 * f x ^ 2) S μ from
      (hdf.const_mul (2 * A ^ 2)).add (hfs.const_mul (2 * B ^ 2)))
    (fun x hx ↦ by simp only [hdzero x hx, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]) (by
      filter_upwards [ae_restrict_of_ae hf.ae_differentiableAt] with x hx
      simp only [abs_pow, abs_norm]
      exact fderiv_mul_sq_bound_of_bounds hx (hζ.differentiable (by norm_num) x) hA hB (ha x) (hb x))
  refine ⟨hi.1, hid.1, ?_, ?_⟩
  · simpa only [integral_const_mul] using hi.2
  · simpa only [integral_add (hdf.const_mul _) (hfs.const_mul _), integral_const_mul] using hid.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeProductCoordinates : Plane ≃L[ℝ] ℝ × ℝ :=
  Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.trans Complex.equivRealProdCLM

lemma planeProductCoordinates_measurePreserving : MeasurePreserving planeProductCoordinates :=
  Complex.volume_preserving_equiv_real_prod.comp Complex.orthonormalBasisOneI.repr.symm.measurePreserving

def planeSquare (R : ℝ) : Set Plane :=
  planeProductCoordinates ⁻¹' (Icc (-R) R ×ˢ Icc (-R) R)

lemma isCompact_planeSquare (R : ℝ) : IsCompact (planeSquare R) :=
  planeProductCoordinates.toHomeomorph.isClosedEmbedding.isCompact_preimage
    (isCompact_Icc.prod isCompact_Icc)

lemma planeSquare_measurePreserving (R : ℝ) :
    MeasurePreserving planeProductCoordinates
      (volume.restrict (planeSquare R))
      ((volume.restrict (Icc (-R) R)).prod (volume.restrict (Icc (-R) R))) := by
  have h := planeProductCoordinates_measurePreserving.restrict_preimage
    (s := Icc (-R) R ×ˢ Icc (-R) R)
    (measurableSet_Icc.prod measurableSet_Icc)
  simpa only [planeSquare, Measure.prod_restrict, ← Measure.volume_eq_prod] using h

theorem plane_square_poincare {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {R : ℝ} (hR : 0 < R) :
    (∫ x in planeSquare R,
      (f x - (∫ y in planeSquare R, f y) / (2 * R) ^ 2) ^ 2) ≤
      16 * R ^ 2 * ‖planeProductCoordinates.symm.toContinuousLinearMap‖ ^ 2 *
        (∫ x in planeSquare R, ‖fderiv ℝ f x‖ ^ 2) := by
  let L := planeProductCoordinates.symm
  let ν := (volume.restrict (Icc (-R) R)).prod (volume.restrict (Icc (-R) R))
  have hL : MeasurePreserving L ν (volume.restrict (planeSquare R)) :=
    (planeSquare_measurePreserving R).symm planeProductCoordinates.toHomeomorph.toMeasurableEquiv
  have hLip : LipschitzWith (K * ‖L.toContinuousLinearMap‖₊) (f ∘ L) :=
    hf.comp L.toContinuousLinearMap.lipschitzWith
  have hp := lipschitz_box_poincare_fderiv hLip (by linarith : -R < R)
  change (∫ x, (f (L x) - (∫ y, f (L y) ∂ν) / (R - -R) ^ 2) ^ 2 ∂ν) ≤
    4 * (R - -R) ^ 2 * ∫ x, ‖fderiv ℝ (f ∘ L) x‖ ^ 2 ∂ν at hp
  have hmean := hL.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding f
  rw [hmean] at hp
  have hh := hL.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun x ↦ (f x - (∫ y in planeSquare R, f y) / (R - -R) ^ 2) ^ 2)
  rw [hh] at hp
  have hleft : (∫ x, ‖fderiv ℝ (f ∘ L) x‖ ^ 2 ∂ν) ≤
      ‖L.toContinuousLinearMap‖ ^ 2 * ∫ x in planeSquare R, ‖fderiv ℝ f x‖ ^ 2 := by
    let : IsFiniteMeasure (volume.restrict (planeSquare R)) :=
      isFiniteMeasure_restrict.mpr (isCompact_planeSquare R).measure_lt_top.ne
    have hd : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) (volume.restrict (planeSquare R)) :=
      lipschitz_fderiv_sq_integrable hf
    have hdL := (hL.integrable_comp hd.aestronglyMeasurable).mpr hd
    have hi := lipschitz_fderiv_sq_integrable (μ := ν) hLip
    have he := integral_mono_ae hi (hdL.const_mul (‖L.toContinuousLinearMap‖ ^ 2)) (by
      filter_upwards [hL.quasiMeasurePreserving.ae (ae_restrict_of_ae hf.ae_differentiableAt)] with x hx
      rw [fderiv_comp x hx L.differentiableAt, L.fderiv]
      have hb := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ f (L x)) L.toContinuousLinearMap
      have hpos := norm_nonneg ((fderiv ℝ f (L x)).comp L.toContinuousLinearMap)
      have hs := pow_le_pow_left₀ hpos hb 2
      simpa only [Function.comp_apply, mul_pow, mul_comm] using hs)
    simp only [integral_const_mul, Function.comp_apply] at he
    rw [hL.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun x ↦ ‖fderiv ℝ f x‖ ^ 2)] at he
    exact he
  have he := mul_le_mul_of_nonneg_left hleft (by positivity : 0 ≤ 4 * (R - -R) ^ 2)
  have he' := hp.trans he
  have hr : R - -R = 2 * R := by ring
  rw [hr] at he'
  calc
    _ ≤ 4 * (2 * R) ^ 2 * (‖L.toContinuousLinearMap‖ ^ 2 *
        ∫ x in planeSquare R, ‖fderiv ℝ f x‖ ^ 2) := he'
    _ = _ := by dsimp [L]; ring

lemma planeSquare_volume (R : ℝ) (hR : 0 ≤ R) :
    (volume : Measure Plane).real (planeSquare R) = (2 * R) ^ 2 := by
  have h := planeProductCoordinates_measurePreserving.measure_preimage
    (s := Icc (-R) R ×ˢ Icc (-R) R)
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet
  change (volume : Measure Plane) (planeSquare R) = _ at h
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc] at h
  rw [measureReal_def, h, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def planarCoordinateDivergence (X Y : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ X z (1,0) + fderiv ℝ Y z (0,1)

lemma triangle_piola_derivatives {X Y : ℝ × ℝ → ℝ}
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) (s t : ℝ) :
    deriv (fun v : ℝ ↦ X (s*v,s)-v*Y (s*v,s)) t +
      deriv (fun u : ℝ ↦ u*Y (u*t,u)) s =
      s*planarCoordinateDivergence X Y (s*t,s) := by
  have ht : HasDerivAt (fun v : ℝ ↦ (s*v,s)) (s,0) t :=
    by simpa using ((hasDerivAt_id t).const_mul s).prodMk (hasDerivAt_const t s)
  have hs : HasDerivAt (fun u : ℝ ↦ (u*t,u)) (t,1) s :=
    by simpa using ((hasDerivAt_id s).mul_const t).prodMk (hasDerivAt_id s)
  have hxt := (hX (s*t,s)).hasFDerivAt.comp_hasDerivAt t ht
  have hyt := (hY (s*t,s)).hasFDerivAt.comp_hasDerivAt t ht
  have hys := (hY ((fun u : ℝ ↦ (u*t,u)) s)).hasFDerivAt.comp_hasDerivAt (f := fun u : ℝ ↦ (u*t,u)) s hs
  have hd1 := (hxt.sub ((hasDerivAt_id t).mul hyt)).deriv
  have hd2 := ((hasDerivAt_id s).mul hys).deriv
  simp only [Function.comp_def,id_eq] at hd1 hd2
  erw [hd1,hd2]
  have he1 : ((s,0) : ℝ × ℝ) = s • ((1,0) : ℝ × ℝ) := by ext <;> simp
  have he2 : ((t,1) : ℝ × ℝ) = t • ((1,0) : ℝ × ℝ)+((0,1) : ℝ × ℝ) := by ext <;> simp
  rw [he1,he2,map_smul,map_smul,map_add,map_smul]
  dsimp [planarCoordinateDivergence]
  ring

lemma continuous_interval_integral_swap {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, f (x,y)) = ∫ y in c..d, ∫ x in a..b, f (x,y) := by
  simp only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict,← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma hasDerivAt_coordinate_left {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ f (t,y)) (fderiv ℝ f (x,y) (1,0)) x := by
  simpa only [Function.comp_def,id_eq] using
    (hf (x,y)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

lemma hasDerivAt_coordinate_right {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ f (x,t)) (fderiv ℝ f (x,y) (0,1)) y := by
  simpa only [Function.comp_def,id_eq] using
    (hf (x,y)).hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

lemma rectangle_coordinate_divergence {X Y : ℝ × ℝ → ℝ}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, planarCoordinateDivergence X Y (x,y)) =
      (∫ y in c..d, X (b,y)-X (a,y)) + (∫ x in a..b, Y (x,d)-Y (x,c)) := by
  have hDX : Continuous (fun z : ℝ × ℝ ↦ fderiv ℝ X z (1,0)) :=
    (hX.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDY : Continuous (fun z : ℝ × ℝ ↦ fderiv ℝ Y z (0,1)) :=
    (hY.continuous_fderiv (by simp)).clm_apply continuous_const
  have hXint : (∫ x in a..b, ∫ y in c..d, fderiv ℝ X (x,y) (1,0)) =
      ∫ y in c..d, X (b,y)-X (a,y) := by
    rw [continuous_interval_integral_swap hDX hab hcd]
    apply intervalIntegral.integral_congr
    intro y _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ hasDerivAt_coordinate_left (hX.differentiable (by simp)) x y)
      ((hDX.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  have hYint (x : ℝ) : (∫ y in c..d, fderiv ℝ Y (x,y) (0,1)) = Y (x,d)-Y (x,c) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ ↦ hasDerivAt_coordinate_right (hY.differentiable (by simp)) x y)
      ((hDY.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  have hsum (x : ℝ) : (∫ y in c..d, planarCoordinateDivergence X Y (x,y)) =
      (∫ y in c..d, fderiv ℝ X (x,y) (1,0)) + (Y (x,d)-Y (x,c)) := by
    have hcX : Continuous (fun y : ℝ ↦ fderiv ℝ X (x,y) (1,0)) := hDX.comp (continuous_const.prodMk continuous_id)
    have hcY : Continuous (fun y : ℝ ↦ fderiv ℝ Y (x,y) (0,1)) := hDY.comp (continuous_const.prodMk continuous_id)
    rw [show (fun y ↦ planarCoordinateDivergence X Y (x,y)) =
      (fun y ↦ fderiv ℝ X (x,y) (1,0)+fderiv ℝ Y (x,y) (0,1)) from rfl,
      intervalIntegral.integral_add
        (hcX.intervalIntegrable _ _) (hcY.intervalIntegrable _ _),hYint]
  simp_rw [hsum]
  have hintX : IntervalIntegrable (fun x ↦ ∫ y in c..d, fderiv ℝ X (x,y) (1,0)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hi : Integrable (fun z : ℝ × ℝ ↦ fderiv ℝ X z (1,0))
        ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
      rw [Measure.prod_restrict,← Measure.volume_eq_prod]
      exact (hDX.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    simp_rw [intervalIntegral.integral_of_le hcd]
    exact hi.integral_prod_left
  have hc : Continuous (fun x : ℝ ↦ Y (x,d)-Y (x,c)) := by fun_prop
  rw [intervalIntegral.integral_add hintX (hc.intervalIntegrable _ _),hXint]

theorem triangle_coordinate_divergence {X Y : ℝ × ℝ → ℝ}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ s in (0 : ℝ)..b, ∫ x in (s*l)..(s*u), planarCoordinateDivergence X Y (x,s)) =
      (∫ s in (0 : ℝ)..b, (X (s*u,s)-u*Y (s*u,s))-(X (s*l,s)-l*Y (s*l,s))) +
      (∫ x in (b*l)..(b*u), Y (x,b)) := by
  let G : ℝ × ℝ → ℝ := fun z ↦ z.1*Y (z.1*z.2,z.1)
  let H : ℝ × ℝ → ℝ := fun z ↦ X (z.1*z.2,z.1)-z.2*Y (z.1*z.2,z.1)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by dsimp [G]; fun_prop
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by dsimp [H]; fun_prop
  have hdiv (s t : ℝ) : planarCoordinateDivergence G H (s,t) =
      s*planarCoordinateDivergence X Y (s*t,s) := by
    rw [planarCoordinateDivergence,← (hasDerivAt_coordinate_left (hG.differentiable (by simp)) s t).deriv,
      ← (hasDerivAt_coordinate_right (hH.differentiable (by simp)) s t).deriv]
    dsimp only [G,H]
    rw [add_comm]
    exact triangle_piola_derivatives (hX.differentiable (by simp)) (hY.differentiable (by simp)) s t
  have he := rectangle_coordinate_divergence hG hH hb hlu
  simp_rw [hdiv] at he
  have hscale (s : ℝ) : (∫ t in l..u, s*planarCoordinateDivergence X Y (s*t,s)) =
      ∫ x in (s*l)..(s*u), planarCoordinateDivergence X Y (x,s) := by
    rw [intervalIntegral.integral_const_mul]
    exact intervalIntegral.smul_integral_comp_mul_left (fun x ↦ planarCoordinateDivergence X Y (x,s)) s
  simp_rw [hscale] at he
  have hg : (∫ t in l..u, G (b,t)-G (0,t)) = ∫ x in (b*l)..(b*u), Y (x,b) := by
    simp only [G,zero_mul,sub_zero]
    rw [intervalIntegral.integral_const_mul]
    exact intervalIntegral.smul_integral_comp_mul_left (fun x ↦ Y (x,b)) b
  rw [hg] at he
  simpa only [H,add_comm] using he

end CubicTorus

end
end

end

end OAI
