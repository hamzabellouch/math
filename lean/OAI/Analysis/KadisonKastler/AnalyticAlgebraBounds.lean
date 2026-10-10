import OAI.Analysis.KadisonKastler.ProbabilityMatrixDistance
import OAI.Analysis.KadisonKastler.PoissonProductEstimates
import OAI.Analysis.KadisonKastler.HardyPoissonProducts

namespace OAI

/-! # Algebra errors of the demodulated analytic products

The Hardy product identity follows from evaluation and preservation of
the frequency nest. The resulting norm estimates pass from boundary
algebra distance to positive-height distance.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance analyticAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance analyticAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] in
/-- Perturbing both factors gives the boundary sandwich error. -/
theorem norm_sandwich_sub_of_contractions
    (a b u v x : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (ha : ‖a - u‖ ≤ δ) (hb : ‖b - v‖ ≤ δ) :
    ‖a * x * b - u * x * v‖ ≤ (2 * δ + δ ^ 2) * ‖x‖ := by
  have han : ‖a‖ ≤ 1 + δ := by
    have h := norm_sub_le_norm_sub_add_norm_sub a u (0 : H →L[ℂ] H)
    simp only [sub_zero] at h
    linarith
  have he : a * x * b - u * x * v = a * x * (b - v) + (a - u) * x * v := by
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖a * x * (b - v)‖ + ‖(a - u) * x * v‖ := norm_add_le _ _
    _ ≤ (‖a‖ * ‖x‖) * ‖b - v‖ + (‖a - u‖ * ‖x‖) * ‖v‖ := add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ ≤ ((1 + δ) * ‖x‖) * δ + (δ * ‖x‖) * 1 := add_le_add
      (mul_le_mul (mul_le_mul_of_nonneg_right han (norm_nonneg _)) hb
        (norm_nonneg _) (by positivity))
      (mul_le_mul (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hv
        (norm_nonneg _) (by positivity))
    _ = _ := by ring

omit [CompleteSpace H] in
theorem sandwich_vector_measurable
    (B S : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun s => B s ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun s => S s ξ) volume) (x : H →L[ℂ] H) :
    ∀ ξ, AEStronglyMeasurable (fun s => (B s * x * S s) ξ) volume := by
  intro ξ
  exact aestronglyMeasurable_field_apply B hB _
    (x.continuous.comp_aestronglyMeasurable (hS ξ))

omit [CompleteSpace H] in
theorem ae_norm_sandwich_le
    (B S : ℝ → H →L[ℂ] H) {CB CS : ℝ} (hCB : 0 ≤ CB)
    (hB : ∀ᵐ s, ‖B s‖ ≤ CB) (hS : ∀ᵐ s, ‖S s‖ ≤ CS) (x : H →L[ℂ] H) :
    ∀ᵐ s, ‖B s * x * S s‖ ≤ CB * ‖x‖ * CS := by
  filter_upwards [hB, hS] with s hb hs
  exact ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))).trans
      (mul_le_mul (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) hs
        (norm_nonneg _) (by positivity))

/-- The actual Poisson average of a product inherits its boundary algebra
error. This is the step for which no measurable nearest points are chosen. -/
theorem infDist_poisson_sandwich_le
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun s => B s ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun s => S s ξ) volume)
    {CB CS : ℝ} (hCB : 0 ≤ CB)
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    {δ e : ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (x : H →L[ℂ] H)
    (hnear : ∀ᵐ s, Metric.infDist (U s * x * V s) (M : Set (H →L[ℂ] H)) ≤ e * ‖x‖)
    (t r : ℝ) (hr : 0 < r) :
    Metric.infDist
      (measurablePoissonAverage (fun s => B s * x * S s)
        (sandwich_vector_measurable B S hB hS x) (CB * ‖x‖ * CS)
        (ae_norm_sandwich_le B S hCB hb hs x) t r hr)
      (M : Set (H →L[ℂ] H)) ≤ (e + 2 * δ + δ ^ 2) * ‖x‖ := by
  apply infDist_measurablePoissonAverage_le _ _ _ _ M hDistance (by positivity)
  filter_upwards [hnear, hu, hv, hBU, hSV] with s hn hu hv hBU hSV
  have h := Metric.infDist_le_infDist_add_dist
    (x := B s * x * S s) (y := U s * x * V s) (s := (M : Set (H →L[ℂ] H)))
  rw [dist_eq_norm] at h
  exact (h.trans (add_le_add hn
    (norm_sandwich_sub_of_contractions _ _ _ _ x hδ hu hv hBU hSV))).trans_eq (by ring)

/-- The published Hardy evaluation and actual frequency preservation give
the quantitative demodulated algebra error at every positive height. -/
private theorem infDist_demodulated_sandwich_le_of_product_identity
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun s => B s ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun s => S s ξ) volume)
    {CB CS : ℝ} (hCB : 0 ≤ CB)
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    {δ e : ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (x : H →L[ℂ] H)
    (hnear : ∀ᵐ s, Metric.infDist (U s * x * V s) (M : Set (H →L[ℂ] H)) ≤ e * ‖x‖)
    (t r : ℝ) (hr : 0 < r)
    (hproduct : measurablePoissonAverage B hB CB hb t r hr * x *
        measurablePoissonAverage S hS CS hs t r hr =
      measurablePoissonAverage (fun s => B s * x * S s)
        (sandwich_vector_measurable B S hB hS x) (CB * ‖x‖ * CS)
        (ae_norm_sandwich_le B S hCB hb hs x) t r hr) :
    Metric.infDist
      (demodulatedPoissonAverage B hB CB hb t r hr * x *
        demodulatedPoissonAverage S hS CS hs t r hr)
      (M : Set (H →L[ℂ] H)) ≤ (Real.exp r) ^ 2 * ((e + 2 * δ + δ ^ 2) * ‖x‖) := by
  let z : ℂ := (Real.exp r : ℂ) * star (Circle.exp t : ℂ)
  have hz : ‖z‖ = Real.exp r := by
    change ‖(Real.exp r : ℂ) * star (Circle.exp t : ℂ)‖ = Real.exp r
    rw [norm_mul, norm_star, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos r)]
  have hid : demodulatedPoissonAverage B hB CB hb t r hr * x *
      demodulatedPoissonAverage S hS CS hs t r hr =
    z ^ 2 • measurablePoissonAverage (fun s => B s * x * S s)
      (sandwich_vector_measurable B S hB hS x) (CB * ‖x‖ * CS)
      (ae_norm_sandwich_le B S hCB hb hs x) t r hr := by
    simp only [demodulatedPoissonAverage, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hproduct]
    simp only [z, pow_two]
  rw [hid, infDist_smul_algebra, norm_pow, hz]
  exact mul_le_mul_of_nonneg_left
    (infDist_poisson_sandwich_le M hDistance B S U V hB hS hCB hb hs hδ he
      hu hv hBU hSV x hnear t r hr) (sq_nonneg _)

theorem infDist_demodulated_sandwich_le
    [TopologicalSpace.SeparableSpace H]
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun s => B s ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun s => S s ξ) volume)
    {CB CS : ℝ} (hCB : 0 ≤ CB)
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    {δ e : ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (x : H →L[ℂ] H)
    (hnear : ∀ᵐ s, Metric.infDist (U s * x * V s) (M : Set (H →L[ℂ] H)) ≤ e * ‖x‖)
    (t r : ℝ) (hr : 0 < r)
    (hBpres : PreservesProjectionNest (regularFrequencyNest (H := H))
      (regularFieldOperator volume B hB CB hb))
    (hSpres : PreservesProjectionNest (regularFrequencyNest (H := H))
      (regularFieldOperator volume S hS CS hs)) :
    Metric.infDist
      (demodulatedPoissonAverage B hB CB hb t r hr * x *
        demodulatedPoissonAverage S hS CS hs t r hr)
      (M : Set (H →L[ℂ] H)) ≤ (Real.exp r) ^ 2 * ((e + 2 * δ + δ ^ 2) * ‖x‖) := by
  let TB : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularFieldOperator volume B hB CB hb
  let TS : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularFieldOperator volume S hS CS hs
  have hBT : RepresentsOperatorField volume B TB := regularFieldOperator_represents volume B hB CB hb
  have hST : RepresentsOperatorField volume S TS := regularFieldOperator_represents volume S hS CS hs
  have hproduct := measurablePoissonAverage_sandwich_of_hardy hHardy B S hB hS CB CS hb hs
    TB TS hBT hST hBpres hSpres x
    (sandwich_vector_measurable B S hB hS x) (CB * ‖x‖ * CS)
    (ae_norm_sandwich_le B S hCB hb hs x) t r hr
  exact infDist_demodulated_sandwich_le_of_product_identity
    M hDistance B S U V hB hS hCB hb hs hδ he hu hv hBU hSV x hnear t r hr hproduct

end

end KadisonKastler

end OAI
