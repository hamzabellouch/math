import OAI.Geometry.RCD.Heat.HeatOffDiagonalL2
import OAI.Geometry.RCD.Heat.HeatDetailedBalance

namespace OAI

/-! # Gaussian decay of the actual transition mass between separated sets

The estimate is a consequence of the weighted Cheeger semigroup bound.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem indicatorConstLp_norm_eq_sqrt {S : Set X} (hS : MeasurableSet S)
    (hfin : μ S ≠ ∞) :
    ‖indicatorConstLp 2 hS hfin (1 : ℝ)‖ = Real.sqrt (μ.real S) := by
  rw [norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat, Real.sqrt_eq_rpow]

namespace NoncollapsedRCD

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonMeasure_set_pair (t : ℝ) (ht : 0 < t)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : hausdorff n X A ≠ ∞) (hBf : hausdorff n X B ≠ ∞) :
    (∫ x in B, (hX.heatRadonMeasure hn p t ht x).real A ∂hausdorff n X) =
      inner ℝ (heatAt (hausdorff n X) hX.quadratic t (indicatorConstLp 2 hA hAf (1 : ℝ)))
        (indicatorConstLp 2 hB hBf (1 : ℝ)) := by
  let f := indicatorConstLp 2 hA hAf (1 : ℝ)
  let g := indicatorConstLp 2 hB hBf (1 : ℝ)
  have hf := indicatorConstLp_abs_le_one (hausdorff n X) hA hAf
  have hrep : (fun x => (hX.heatRadonMeasure hn p t ht x).real A) =ᵐ[hausdorff n X]
      heatAt (hausdorff n X) hX.quadratic t f := by
    filter_upwards [hX.boundedHeat_represents hn p f ⟨1, hf⟩ t ht] with x hx
    rw [← hX.heatRadonMeasure_integral_indicator hn p t ht x hA hAf,
      hX.heatRadonMeasure_integral_bounded hn p t ht x f 1 hf, ← hx]
  calc
    _ = ∫ x, g x * (hX.heatRadonMeasure hn p t ht x).real A ∂hausdorff n X :=
      (integral_indicatorConstLp_mul (hausdorff n X) B hB hBf _).symm
    _ = inner ℝ (heatAt (hausdorff n X) hX.quadratic t f) g := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      simp only [hx, Real.inner_apply, mul_comm]

/-- The sharp Davies exponent for transition mass between a source set
inside a ball and an observation set outside a larger concentric ball. -/
theorem heatRadonMeasure_separated_sets (t : ℝ) (ht : 0 < t)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : hausdorff n X A ≠ ∞) (hBf : hausdorff n X B ≠ ∞)
    (q : X) {r R : ℝ} (hnear : ∀ x ∈ A, dist q x ≤ r)
    (hfar : ∀ x ∈ B, R ≤ dist q x) (hrR : r ≤ R) :
    (∫ x in B, (hX.heatRadonMeasure hn p t ht x).real A ∂hausdorff n X) ≤
      Real.exp (-(R-r)^2 / (4*t)) *
        Real.sqrt ((hausdorff n X).real A) * Real.sqrt ((hausdorff n X).real B) := by
  let f := indicatorConstLp 2 hA hAf (1 : ℝ)
  let g := indicatorConstLp 2 hB hBf (1 : ℝ)
  have hf : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist q x ≤ r := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hAf) (c := (1 : ℝ))]
      with x hx
    intro hx0
    by_cases ha : x ∈ A
    · exact hnear x ha
    · simp only [f, hx, indicator_of_notMem ha] at hx0
      exact False.elim (hx0 rfl)
  have hg : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → R ≤ dist q x := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := hBf) (c := (1 : ℝ))]
      with x hx
    intro hx0
    by_cases hb : x ∈ B
    · exact hfar x hb
    · simp only [g, hx, indicator_of_notMem hb] at hx0
      exact False.elim (hx0 rfl)
  rw [hX.heatRadonMeasure_set_pair hn p t ht hA hB hAf hBf]
  calc
    _ ≤ |inner ℝ (heatAt (hausdorff n X) hX.quadratic t f) g| := le_abs_self _
    _ ≤ _ := by
      simpa only [f, g, indicatorConstLp_norm_eq_sqrt] using
        heatAt_radial_pairing (hausdorff n X) hX.quadratic f g q hf hg hrR ht

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
