import OAI.Geometry.RCD.Coordinates.RegularizedGram

namespace OAI

/-!
# Heat averages of the canonical Sobolev Gram form

The published kernel input is the specialization of Jiang--Li--Zhang,
*Heat kernel bounds on metric measure spaces and some applications* (2016),
Section 2.2, printed p. 7, to `L¹ ∩ L²` data and a fixed positive time.
See https://arxiv.org/pdf/1407.5289v2 .
The Gaussian and gradient bounds of Theorem 1.2 and Corollary 1.2 are
separate quantitative inputs, not part of the definition below.
-/

open Set MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

variable [μ.Regular]

/-- The positive-time representative of the actual Cheeger heat semigroup.
The representation is required only for data in `L¹ ∩ L²`.
The convolution fields are the Chapman--Kolmogorov identity in the same
published Section 2.2; integrability records that its nonnegative integral
is finite, rather than relying on the zero convention for undefined integrals. -/
structure IsContinuousHeatKernel (p : ℝ → X → X → ℝ) : Prop where
  nonneg : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y
  continuous_right : ∀ t, 0 < t → ∀ x, Continuous (p t x)
  continuous_joint : ∀ t, 0 < t → Continuous (fun xy : X × X => p t xy.1 xy.2)
  symmetric : ∀ t, 0 < t → ∀ x y, p t x y = p t y x
  integrable : ∀ t, 0 < t → ∀ x, Integrable (p t x) μ
  mass_one : ∀ t, 0 < t → ∀ x, ∫ y, p t x y ∂μ = 1
  convolution_integrable : ∀ s t, 0 < s → 0 < t → ∀ x y,
    Integrable (fun z => p s x z * p t z y) μ
  convolution : ∀ s t, 0 < s → 0 < t → ∀ x y,
    ∫ z, p s x z * p t z y ∂μ = p (s + t) x y
  represents : ∀ t, 0 < t → ∀ f : Lp ℝ 2 μ, Integrable f μ →
    (fun x => ∫ y, p t x y * f y ∂μ) =ᵐ[μ] heatAt μ hQ t f

/-- Existence of a continuous kernel representing the Cheeger heat semigroup. -/
def ContinuousHeatKernelInput : Prop :=
  ∃ p : ℝ → X → X → ℝ, IsContinuousHeatKernel μ hQ p

variable {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

include hp hχ hsχ in
/-- Compact cutoff makes each positive-time heat weight globally bounded;
no uniform Gaussian bound is needed for this existence step. -/
theorem exists_cutoff_heat_weight_bound {t : ℝ} (ht : 0 < t) (x : X) :
    ∃ C : ℝ≥0, ∀ y, ‖χ y * p t x y‖ ≤ C := by
  have hc : Continuous (fun y => χ y * p t x y) := hχ.mul (hp.continuous_right t ht x)
  have hs : HasCompactSupport (fun y => χ y * p t x y) := hsχ.mul_right
  obtain ⟨B, hB⟩ := (hs.isCompact_range hc).isBounded.exists_norm_le
  refine ⟨⟨max B 0, le_max_right _ _⟩, fun y => ?_⟩
  exact (hB _ (mem_range_self y)).trans (le_max_left _ _)

def cutoffHeatWeightBound {t : ℝ} (ht : 0 < t) (x : X) : ℝ≥0 :=
  (exists_cutoff_heat_weight_bound μ hQ hp hχ hsχ ht x).choose

theorem cutoffHeatWeight_le {t : ℝ} (ht : 0 < t) (x y : X) :
    ‖χ y * p t x y‖ ≤ cutoffHeatWeightBound μ hQ hp hχ hsχ ht x :=
  (exists_cutoff_heat_weight_bound μ hQ hp hχ hsχ ht x).choose_spec y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (U : E →L[ℝ] SobolevSpace μ hQ)

/-- The actual cutoff heat average of the Gram field, with the manuscript's
positive scalar regularization. The weight is constructed from the kernel. -/
def cutoffHeatGram {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) : E →L[ℝ] E :=
  regularizedSobolevGram μ hQ U
    ((hχ.mul (hp.continuous_right t ht x)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x))
    (lambda * t)

theorem cutoffHeatGram_energy {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) (v : E) :
    ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda v⟫_ℝ =
      (∫ y, (χ y * p t x y) * (SobolevSpace.minimalSlope μ hQ (U v) y) ^ 2 ∂μ) +
      (lambda * t) * ‖v‖ ^ 2 := by
  exact regularizedSobolevGram_energy μ hQ U _ _ _ v

/-- Whenever a cutoff energy density is represented as an `L¹ ∩ L²`
function, the quadratic form is the actual Cheeger heat semigroup applied
to that density, with precisely the added scalar regularization. -/
theorem cutoffHeatGram_represents_energy {t : ℝ} (ht : 0 < t) (lambda : ℝ)
    (v : E) (f : Lp ℝ 2 μ) (hfi : Integrable f μ)
    (hf : f =ᵐ[μ] fun y => χ y * (SobolevSpace.minimalSlope μ hQ (U v) y) ^ 2) :
    (fun x => ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda v⟫_ℝ) =ᵐ[μ]
      fun x => heatAt μ hQ t f x + (lambda * t) * ‖v‖ ^ 2 := by
  filter_upwards [hp.represents t ht f hfi] with x hx
  rw [cutoffHeatGram_energy]
  have he : (∫ y, (χ y * p t x y) *
      (SobolevSpace.minimalSlope μ hQ (U v) y) ^ 2 ∂μ) =
      ∫ y, p t x y * f y ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [hy]
    ring
  rw [he, hx]

theorem cutoffHeatGram_isPositive (hχpos : ∀ y, 0 ≤ χ y)
    {t : ℝ} (ht : 0 < t) (x : X) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda).IsPositive := by
  apply regularizedSobolevGram_isPositive
  · exact Filter.Eventually.of_forall fun y => mul_nonneg (hχpos y) (hp.nonneg t ht x y)
  · exact mul_nonneg hlambda ht.le

/-- Strict regularization constructs the inverse of every actual heat Gram
operator in finite dimension, at every testing point and positive time. -/
def cutoffHeatGramEquiv [FiniteDimensional ℝ E] (hχpos : ∀ y, 0 ≤ χ y)
    {t : ℝ} (ht : 0 < t) (x : X) {lambda : ℝ} (hlambda : 0 < lambda) : E ≃L[ℝ] E :=
  regularizedSobolevGramEquiv μ hQ U
    ((hχ.mul (hp.continuous_right t ht x)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x))
    (Filter.Eventually.of_forall fun y => mul_nonneg (hχpos y) (hp.nonneg t ht x y))
    (mul_pos hlambda ht)

theorem cutoffHeatGramEquiv_apply [FiniteDimensional ℝ E] (hχpos : ∀ y, 0 ≤ χ y)
    {t : ℝ} (ht : 0 < t) (x : X) {lambda : ℝ} (hlambda : 0 < lambda) (v : E) :
    cutoffHeatGramEquiv μ hQ hp hχ hsχ U hχpos ht x hlambda v =
      cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda v := rfl

end RegularPointCoordinates

end

end OAI
