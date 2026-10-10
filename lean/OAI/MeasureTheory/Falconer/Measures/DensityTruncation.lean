import OAI.MeasureTheory.Falconer.Angular.CapTransport
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-!
# Truncation of radial densities

The integer-cap step `prep:integer-caps` deletes pairs on which either
radial density exceeds a threshold. These lemmas estimate the deleted
original product mass by the Lp moments and bound every remaining fiber
by the threshold times the angular reference measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

private theorem ennreal_le_threshold_tail {t T : ℝ≥0∞} {p : ℝ}
    (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) (ht : T ≤ t) :
    t ≤ T ^ (1 - p) * t ^ p := by
  have hpow := ENNReal.rpow_le_rpow ht (by linarith : 0 ≤ p - 1)
  have hprod : T ^ (p - 1) * t ≤ t ^ p := by
    calc
      T ^ (p - 1) * t ≤ t ^ (p - 1) * t := mul_le_mul_left hpow t
      _ = t ^ ((p - 1) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
      _ = t ^ p := by congr 1; ring
  have hcancel : T ^ (1 - p) * T ^ (p - 1) = 1 := by
    rw [← ENNReal.rpow_add _ _ hT.ne' hTtop]
    convert (ENNReal.rpow_zero : T ^ (0 : ℝ) = 1) using 1
    congr 1
    ring
  calc
    t = (T ^ (1 - p) * T ^ (p - 1)) * t := by rw [hcancel, one_mul]
    _ = T ^ (1 - p) * (T ^ (p - 1) * t) := mul_assoc _ _ _
    _ ≤ T ^ (1 - p) * t ^ p := mul_le_mul_right hprod _

/-- The density mass above `T` is bounded by `T^(1-p)` times its pth moment. -/
theorem density_tail_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (σ.withDensity f) {a | T < f a} ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ := by
  have hS : MeasurableSet {a | T < f a} := measurableSet_lt measurable_const hf
  rw [withDensity_apply _ hS]
  calc
    (∫⁻ a in {a | T < f a}, f a ∂σ) ≤
        ∫⁻ a in {a | T < f a}, T ^ (1 - p) * f a ^ p ∂σ := by
      apply setLIntegral_mono' hS
      intro a ha
      exact ennreal_le_threshold_tail hT hTtop hp ha.le
    _ = T ^ (1 - p) * ∫⁻ a in {a | T < f a}, f a ^ p ∂σ :=
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)
    _ ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ :=
      mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- Truncation leaves a density bounded by the threshold on every cap. -/
theorem truncated_density_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    (T : ℝ≥0∞) (S : Set A) (hS : MeasurableSet S) :
    (σ.withDensity f) (S ∩ {a | f a ≤ T}) ≤ T * σ S := by
  have hlow : MeasurableSet {a | f a ≤ T} := measurableSet_le hf measurable_const
  rw [withDensity_apply _ (hS.inter hlow)]
  calc
    (∫⁻ a in S ∩ {a | f a ≤ T}, f a ∂σ) ≤
        ∫⁻ _ in S ∩ {a | f a ≤ T}, T ∂σ := by
      apply setLIntegral_mono' (hS.inter hlow)
      intro a ha
      exact ha.2
    _ = T * σ (S ∩ {a | f a ≤ T}) := by simp
    _ ≤ T * σ S := mul_le_mul_right (measure_mono inter_subset_left) T

/-- The bad pairs for one orientation of a radial kernel. -/
def densityFailure {X Y A : Type*} (f : X × A → ℝ≥0∞)
    (r : X × Y → A) (T : ℝ≥0∞) : Set (X × Y) :=
  {z | T < f (z.1, r z)}

theorem measurableSet_densityFailure {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    {f : X × A → ℝ≥0∞} {r : X × Y → A} (hf : Measurable f) (hr : Measurable r)
    (T : ℝ≥0∞) : MeasurableSet (densityFailure f r T) :=
  measurableSet_lt measurable_const (hf.comp (measurable_fst.prodMk hr))

/-- Fubini measures failure using the original source marginal and the
original pin marginal. There is no normalization of individual fibers. -/
theorem density_failure_product_mass {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (σ : Measure A)
    (f : X × A → ℝ≥0∞) (r : X × Y → A) (hf : Measurable f) (hr : Measurable r)
    (hdensity : ∀ᵐ x ∂μ, ν.map (fun y => r (x, y)) = σ.withDensity (fun a => f (x, a)))
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (μ.prod ν) (densityFailure f r T) ≤
      T ^ (1 - p) * ∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ := by
  rw [Measure.prod_apply (measurableSet_densityFailure hf hr T)]
  calc
    (∫⁻ x, ν (Prod.mk x ⁻¹' densityFailure f r T) ∂μ) ≤
        ∫⁻ x, T ^ (1 - p) * ∫⁻ a, f (x, a) ^ p ∂σ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hdensity] with x hx
      have hfx : Measurable (fun a => f (x, a)) := hf.comp (measurable_const.prodMk measurable_id)
      have hrx : Measurable (fun y => r (x, y)) := hr.comp (measurable_const.prodMk measurable_id)
      change ν ((fun y => r (x, y)) ⁻¹' {a | T < f (x, a)}) ≤ _
      rw [← Measure.map_apply hrx (measurableSet_lt measurable_const hfx), hx]
      exact density_tail_mass σ _ hfx hT hTtop hp
    _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)

/-- Any additional pair restriction preserves the truncated fiber bound. -/
theorem truncated_radial_fiber {Y A : Type*} [MeasurableSpace Y] [MeasurableSpace A]
    (ν : Measure Y) (σ : Measure A) (f : A → ℝ≥0∞) (r : Y → A)
    (hf : Measurable f) (hr : Measurable r) (hdensity : ν.map r = σ.withDensity f)
    (T : ℝ≥0∞) (H : Set Y) (hH : ∀ y ∈ H, f (r y) ≤ T)
    (S : Set A) (hS : MeasurableSet S) :
    ν (H ∩ r ⁻¹' S) ≤ T * σ S := by
  have hset : H ∩ r ⁻¹' S ⊆ r ⁻¹' (S ∩ {a | f a ≤ T}) := by
    rintro y ⟨hy, hSy⟩
    exact ⟨hSy, hH y hy⟩
  calc
    ν (H ∩ r ⁻¹' S) ≤ ν (r ⁻¹' (S ∩ {a | f a ≤ T})) := measure_mono hset
    _ = (σ.withDensity f) (S ∩ {a | f a ≤ T}) := by
      rw [← hdensity, Measure.map_apply hr (hS.inter (measurableSet_le hf measurable_const))]
    _ ≤ T * σ S := truncated_density_mass σ f hf T S hS

/-- Deleting the failures in both orientations costs the sum of the two
integrated radial pth moments. -/
theorem bilateral_density_failure_mass {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (σ : Measure A)
    (f : X × A → ℝ≥0∞) (r : X × Y → A) (g : Y × A → ℝ≥0∞) (s : Y × X → A)
    (hf : Measurable f) (hr : Measurable r) (hg : Measurable g) (hs : Measurable s)
    (hfdensity : ∀ᵐ x ∂μ, ν.map (fun y => r (x, y)) = σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂ν, μ.map (fun x => s (y, x)) = σ.withDensity (fun a => g (y, a)))
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (μ.prod ν) (densityFailure f r T ∪ Prod.swap ⁻¹' densityFailure g s T) ≤
      T ^ (1 - p) * ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ) +
        ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂ν) := by
  have hswap : (μ.prod ν) (Prod.swap ⁻¹' densityFailure g s T) =
      (ν.prod μ) (densityFailure g s T) := by
    rw [← Measure.map_apply measurable_swap (measurableSet_densityFailure hg hs T), Measure.prod_swap]
  calc
    _ ≤ (μ.prod ν) (densityFailure f r T) + (μ.prod ν) (Prod.swap ⁻¹' densityFailure g s T) :=
      measure_union_le _ _
    _ = (μ.prod ν) (densityFailure f r T) + (ν.prod μ) (densityFailure g s T) := by rw [hswap]
    _ ≤ T ^ (1 - p) * (∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ) +
        T ^ (1 - p) * ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂ν :=
      add_le_add (density_failure_product_mass μ ν σ f r hf hr hfdensity hT hTtop hp)
        (density_failure_product_mass ν μ σ g s hg hs hgdensity hT hTtop hp)
    _ = _ := (mul_add _ _ _).symm

/-- The threshold `R^(e/2)` gives a positive power saving in deleted mass
for every `p > 1`; its exponent is exactly `e * (p - 1) / 2`. -/
theorem exists_density_tail_power_bound (M : ℝ≥0∞) (hM : M ≠ ∞)
    {e p : ℝ} (he : 0 < e) (hp : 1 < p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ R : ℝ, 0 < R →
      (ENNReal.ofReal (R ^ (e / 2))) ^ (1 - p) * M ≤
        ENNReal.ofReal (C * R ^ (-c)) := by
  refine ⟨e * (p - 1) / 2, M.toReal + 1, by positivity, by positivity, ?_⟩
  intro R hR
  have hpow : (e / 2) * (1 - p) = -(e * (p - 1) / 2) := by ring
  calc
    (ENNReal.ofReal (R ^ (e / 2))) ^ (1 - p) * M =
        ENNReal.ofReal (M.toReal * R ^ (-(e * (p - 1) / 2))) := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hR _),
        ← Real.rpow_mul hR.le, hpow]
      conv_lhs => rw [← ENNReal.ofReal_toReal hM]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((M.toReal + 1) * R ^ (-(e * (p - 1) / 2))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hR.le _)

@[fun_prop] theorem measurable_radialDirection_joint {d : ℕ} :
    Measurable (fun z : Space d × Space d => radialDirection z.1 z.2) := by
  unfold radialDirection
  fun_prop

end Falconer

end OAI
