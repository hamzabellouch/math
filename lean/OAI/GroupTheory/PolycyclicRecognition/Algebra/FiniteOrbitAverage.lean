import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationarySlope
import Mathlib.Analysis.Convex.Combination

namespace OAI

/-! # Finite convex averages of translates

The same finite data act on actual functions and on their L2 classes. This
allows the averages to be transported to a conditional component measure.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

/-- A finite probability distribution on acting elements. -/
structure FiniteOrbitAverage (G : Type*) where
  index : Type
  [finiteIndex : Fintype index]
  weight : index → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  mass : ∑ i, weight i = 1
  element : index → G

attribute [instance] FiniteOrbitAverage.finiteIndex

variable {G X : Type*} [Group G] [MulAction G X]

/-- The actual finite average, with the inverse convention of the Koopman action. -/
def FiniteOrbitAverage.apply (A : FiniteOrbitAverage G) (f : X → ℝ) (x : X) : ℝ :=
  ∑ i, A.weight i * f ((A.element i)⁻¹ • x)

theorem FiniteOrbitAverage.apply_nonneg (A : FiniteOrbitAverage G) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : X) : 0 ≤ A.apply f x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (A.nonneg i) (hf _))

theorem FiniteOrbitAverage.apply_le_one (A : FiniteOrbitAverage G) (f : X → ℝ)
    (hf : ∀ x, f x ≤ 1) (x : X) : A.apply f x ≤ 1 := by
  calc
    A.apply f x ≤ ∑ i, A.weight i * 1 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf _) (A.nonneg i))
    _ = 1 := by simpa only [mul_one] using A.mass

variable [MeasurableSpace X] [MeasurableConstSMul G X]

theorem FiniteOrbitAverage.measurable_apply (A : FiniteOrbitAverage G) (f : X → ℝ)
    (hf : Measurable f) : Measurable (A.apply f) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul
    (hf.comp (measurable_const_smul (A.element i)⁻¹)))

variable
  (μ : Measure X) [SMulInvariantMeasure G X μ]

/-- The same average of the actual unitary operators. -/
def FiniteOrbitAverage.onL2 (A : FiniteOrbitAverage G) (v : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ∑ i, A.weight i • stationaryPullback μ (A.element i) v

/-- Every vector in the convex hull of an orbit has finite averaging data. -/
theorem exists_finiteOrbitAverage (v w : Lp ℝ 2 μ)
    (hw : w ∈ convexHull ℝ (range (fun g : G => stationaryPullback μ g v))) :
    ∃ A : FiniteOrbitAverage G, A.onL2 μ v = w := by
  obtain ⟨ι, hι, a, z, ha, hs, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hw
  let := hι
  choose g hg using hz
  let A : FiniteOrbitAverage G :=
    { index := ι
      finiteIndex := hι
      weight := a
      nonneg := ha
      mass := hs
      element := g }
  refine ⟨A, ?_⟩
  change (∑ i, a i • stationaryPullback μ (g i) v) = w
  simpa only [hg] using he

/-- Pointwise representatives of the finite Hilbert average. -/
theorem FiniteOrbitAverage.onL2_coe (A : FiniteOrbitAverage G) (v : Lp ℝ 2 μ) :
    (A.onL2 μ v : X → ℝ) =ᵐ[μ] A.apply v := by
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun i : A.index => A.weight i • stationaryPullback μ (A.element i) v)
  have hi (i : A.index) :
      ((A.weight i • stationaryPullback μ (A.element i) v : Lp ℝ 2 μ) : X → ℝ)
        =ᵐ[μ] fun x => A.weight i * v ((A.element i)⁻¹ • x) := by
    have hsm := Lp.coeFn_smul (A.weight i) (stationaryPullback μ (A.element i) v)
    have hp := Lp.coeFn_compMeasurePreserving v (measurePreserving_smul (A.element i)⁻¹ μ)
    filter_upwards [hsm, hp] with x hx hpx
    exact hx.trans (congrArg (fun t : ℝ => A.weight i * t) hpx)
  filter_upwards [hsum, ae_all_iff.2 hi] with x hx hi
  change (A.onL2 μ v) x = ∑ i, A.weight i * v ((A.element i)⁻¹ • x)
  rw [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl (fun i _ => hi i))

end PolycyclicRecognition

end

end OAI
