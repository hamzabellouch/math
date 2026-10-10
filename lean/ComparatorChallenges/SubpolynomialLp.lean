import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
universe u

namespace SubpolynomialLp

def coordinateDistance (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ a, |x a - y a| ^ p) ^ (1 / p)

/-- The universal property used in the definition of d_p(n,D). -/
def GoodDimension (p : ℝ) (n : ℕ) (D : ℝ) (d : ℕ) : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
    (x : Fin n → @Lp Ω ℝ mΩ _ (ENNReal.ofReal p) μ),
    Function.Injective x →
    ∃ (y : Fin n → Fin d → ℝ) (s : ℝ), 0 < s ∧
      ∀ i j, s * ‖x i - x j‖ ≤ coordinateDistance p (y i) (y j) ∧
        coordinateDistance p (y i) (y j) ≤ D * s * ‖x i - x j‖

/-- The least universal coordinate dimension. The theorem also asserts that
this least dimension has the defining property, ruling out an empty infimum. -/
def dimension (p : ℝ) (n : ℕ) (D : ℝ) : ℕ :=
  sInf {d : ℕ | GoodDimension.{u} p n D d}

def gamma (p : ℝ) : ℝ := if p < 2 then 2 - p else 1 - 2 / p

/-- The universal coordinate dimension bounds and their logarithmic limits. -/
theorem source_main (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) :
    (∀ D : ℝ, 1 < D → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      GoodDimension.{u} p n D (dimension.{u} p n D) ∧
      Real.log (n : ℝ) / Real.log (1 + 2 * D) ≤ (dimension.{u} p n D : ℝ) ∧
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C * Real.log (n : ℝ) ^ gamma p)) ∧
    (∀ n : ℕ, 9 ≤ n →
      GoodDimension.{u} p n 1 (dimension.{u} p n 1) ∧
      ((n - 1) / 4) ^ 2 ≤ dimension.{u} p n 1 ∧
      dimension.{u} p n 1 ≤ n.choose 2) ∧
    (∀ D : ℝ, 1 ≤ D →
      Tendsto (fun n : ℕ => Real.log (dimension.{u} p n D : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (if 1 < D then 0 else 2))) := by
  sorry

end SubpolynomialLp

end

end OAI
