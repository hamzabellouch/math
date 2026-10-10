import OAI.Geometry.RCD.Heat.ActualHeatGrams

namespace OAI

/-!
# Positive-time kernel rows as actual L2 and Sobolev functions

The only kernel input is `IsContinuousHeatKernel`, including the precise
Chapman--Kolmogorov identity of Jiang--Li--Zhang (2016), Section 2.2,
printed p. 7. Square integrability, the L2 semigroup evolution and positive-time
Sobolev regularity are consequences, rather than extra kernel assumptions.
-/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal Topology

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

include hp in
theorem heatKernel_memLp {t : ℝ} (ht : 0 < t) (x : X) : MemLp (p t x) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hp.continuous_right t ht x).aestronglyMeasurable).mpr
  convert hp.convolution_integrable t t ht ht x x using 1
  ext z
  rw [hp.symmetric t ht z x, pow_two]

/-- The actual L2 kernel row. The value at nonpositive times is unused. -/
def heatKernelRow (t : ℝ) (x : X) : Lp ℝ 2 μ :=
  if ht : 0 < t then (heatKernel_memLp μ hQ hp ht x).toLp (p t x) else 0

include hp in
theorem heatKernelRow_coe {t : ℝ} (ht : 0 < t) (x : X) :
    heatKernelRow μ hQ hp t x =ᵐ[μ] p t x := by
  simp only [heatKernelRow, dite_eq_left ht]
  exact MemLp.coeFn_toLp _

include hp in
theorem heatKernelRow_inner {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : X) :
    ⟪heatKernelRow μ hQ hp s x, heatKernelRow μ hQ hp t y⟫_ℝ = p (s + t) x y := by
  rw [L2.inner_def]
  calc
    (∫ z, ⟪heatKernelRow μ hQ hp s x z, heatKernelRow μ hQ hp t y z⟫_ℝ ∂μ) =
        ∫ z, p s x z * p t z y ∂μ := by
      apply integral_congr_ae
      filter_upwards [heatKernelRow_coe μ hQ hp hs x,
        heatKernelRow_coe μ hQ hp ht y] with z hz hz'
      simp only [hz, hz', RCLike.inner_apply, conj_trivial]
      rw [hp.symmetric t ht y z, mul_comm]
    _ = p (s + t) x y := hp.convolution s t hs ht x y

include hp in
theorem heatKernelRow_norm_sq {t : ℝ} (ht : 0 < t) (x : X) :
    ‖heatKernelRow μ hQ hp t x‖ ^ 2 = p (2 * t) x x := by
  rw [← real_inner_self_eq_norm_sq, heatKernelRow_inner μ hQ hp ht ht]
  congr 1
  ring

include hp in
theorem heatKernelRow_evolves {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : X) :
    heatAt μ hQ s (heatKernelRow μ hQ hp t x) = heatKernelRow μ hQ hp (s + t) x := by
  apply Lp.ext
  have hi : Integrable (heatKernelRow μ hQ hp t x) μ :=
    (hp.integrable t ht x).congr (heatKernelRow_coe μ hQ hp ht x).symm
  filter_upwards [hp.represents s hs (heatKernelRow μ hQ hp t x) hi,
    heatKernelRow_coe μ hQ hp (add_pos hs ht) x] with y hy hrow
  rw [← hy, hrow]
  calc
    (∫ z, p s y z * heatKernelRow μ hQ hp t x z ∂μ) =
        ∫ z, p s y z * p t z x ∂μ := by
      apply integral_congr_ae
      filter_upwards [heatKernelRow_coe μ hQ hp ht x] with z hz
      rw [hz, hp.symmetric t ht x z]
    _ = p (s + t) y x := hp.convolution s t hs ht y x
    _ = p (s + t) x y := hp.symmetric (s + t) (add_pos hs ht) y x

/-- Positive-time kernel rows belong to the actual Cheeger Sobolev space. -/
def heatKernelSobolev (t : ℝ) (ht : 0 < t) (x : X) : SobolevSpace μ hQ :=
  heatSobolev μ hQ (t / 2) (half_pos ht) (heatKernelRow μ hQ hp (t / 2) x)

include hp in
theorem heatKernelSobolev_toLp {t : ℝ} (ht : 0 < t) (x : X) :
    SobolevSpace.toLp μ hQ (heatKernelSobolev μ hQ hp t ht x) =
      heatKernelRow μ hQ hp t x := by
  rw [heatKernelSobolev, heatSobolev_toLp,
    heatKernelRow_evolves μ hQ hp (half_pos ht) (half_pos ht)]
  congr 1
  ring

include hp in
theorem heatKernelSobolev_coe {t : ℝ} (ht : 0 < t) (x : X) :
    SobolevSpace.toLp μ hQ (heatKernelSobolev μ hQ hp t ht x) =ᵐ[μ] p t x := by
  rw [heatKernelSobolev_toLp]
  exact heatKernelRow_coe μ hQ hp ht x

include hp in
theorem heatKernelSobolev_weak_laplacian {t : ℝ} (ht : 0 < t) (x : X) :
    IsWeakLaplacian μ hQ (heatKernelSobolev μ hQ hp t ht x)
      (-heatGenerator μ hQ (t / 2) (half_pos ht) (heatKernelRow μ hQ hp (t / 2) x)) :=
  heatSobolev_weak_laplacian μ hQ (t / 2) (half_pos ht) _

include hp in
/-- Spatial continuity in L2, including at every source point. -/
theorem heatKernelRow_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (heatKernelRow μ hQ hp t) := by
  rw [continuous_iff_continuous_dist]
  have hd (x y : X) :
      dist (heatKernelRow μ hQ hp t x) (heatKernelRow μ hQ hp t y) =
        Real.sqrt (p (2 * t) x x - 2 * p (2 * t) x y + p (2 * t) y y) := by
    rw [dist_eq_norm, show 2 * t = t + t by ring, ← heatKernelRow_inner μ hQ hp ht ht x y,
      show t + t = 2 * t by ring,
      ← heatKernelRow_norm_sq μ hQ hp ht x, ← heatKernelRow_norm_sq μ hQ hp ht y]
    rw [ ← norm_sub_sq_real, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hd]
  have hc := hp.continuous_joint (2 * t) (by positivity)
  exact ((hc.comp (continuous_fst.prodMk continuous_fst)).sub
    (continuous_const.mul hc) |>.add
      (hc.comp (continuous_snd.prodMk continuous_snd))).sqrt

/-- The canonical positive-time continuous representative defined by the kernel. -/
def kernelHeat (t : ℝ) (f : Lp ℝ 2 μ) (x : X) : ℝ :=
  ⟪heatKernelRow μ hQ hp t x, f⟫_ℝ

include hp in
theorem kernelHeat_continuous {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    Continuous (kernelHeat μ hQ hp t f) :=
  (heatKernelRow_continuous μ hQ hp ht).inner continuous_const

include hp in
theorem kernelHeat_eq_integral {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) (x : X) :
    kernelHeat μ hQ hp t f x = ∫ y, p t x y * f y ∂μ := by
  rw [kernelHeat, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [heatKernelRow_coe μ hQ hp ht x] with y hy
  simp only [hy, RCLike.inner_apply, conj_trivial]
  ring

include hp in
theorem kernelHeat_represents {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ)
    (hf : Integrable f μ) : kernelHeat μ hQ hp t f =ᵐ[μ] heatAt μ hQ t f := by
  filter_upwards [hp.represents t ht f hf] with x hx
  rw [kernelHeat_eq_integral μ hQ hp ht f]
  exact hx

end RegularPointCoordinates

end

end OAI
