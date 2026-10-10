import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteGaussian
import Mathlib.Probability.Independence.InfinitePi

namespace OAI

/-!
# Independent finite heads and infinite tails

The restrictions of a product sample to disjoint index sets are independent.
For complex Gaussian coordinates, every nonempty open weighted finite-head
event has positive probability. These facts apply to any countable Fourier
indexing, including the twelve-dimensional frequency lattice.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DefocusingNLS

/-- Product coordinates on disjoint sets remain independent as entire vectors,
including when one of the index sets is infinite. -/
theorem independent_product_restrictions {ι X : Type*} [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Set ι) (hST : Disjoint S T) :
    IndepFun S.domRestrict T.domRestrict (Measure.infinitePi μ) := by
  rw [IndepFun_iff_Indep]
  change Indep
    ((inferInstance : MeasurableSpace (S → X)).comap (fun z (i : S) => z i))
    ((inferInstance : MeasurableSpace (T → X)).comap (fun z (i : T) => z i))
    (Measure.infinitePi μ)
  rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
  simp_rw [iSup_subtype]
  apply indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) _ hST
  exact (iIndepFun_iff_iIndep (fun _ : ι => inferInstance)
    (fun i z => z i) (Measure.infinitePi μ)).mp
    (iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop))

/-- In particular, a finite head and its full complementary tail are independent. -/
theorem independent_product_head_tail {ι X : Type*} [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (S : Finset ι) :
    IndepFun S.restrict (Set.compl (S : Set ι)).domRestrict
      (Measure.infinitePi μ) := by
  exact independent_product_restrictions μ (S : Set ι) (S : Set ι)ᶜ disjoint_compl_right

/-- Law of a nonzero weighted finite head of an infinite Gaussian sample. -/
theorem weighted_gaussian_head_law {ι : Type*} (S : Finset ι)
    (v : ℝ≥0) (w : S → ℂ) :
    (Measure.infinitePi (fun _ : ι => complexGaussian v)).map
      (fun z : ι → ℂ => fun i : S => w i * z i) =
    (Measure.pi (fun _ : S => complexGaussian v)).map
      (fun z : S → ℂ => fun i => w i * z i) := by
  calc
    _ = ((Measure.infinitePi (fun _ : ι => complexGaussian v)).map S.restrict).map
        (fun z : S → ℂ => fun i => w i * z i) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by rw [Measure.infinitePi_map_restrict]

/-- Positive probability of every prescribed open finite-head neighborhood. -/
theorem weighted_gaussian_head_open_pos {ι : Type*} (S : Finset ι)
    {v : ℝ≥0} (hv : v ≠ 0) (w : S → ℂ) (hw : ∀ i, w i ≠ 0)
    (U : Set (S → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < Measure.infinitePi (fun _ : ι => complexGaussian v)
      ((fun z : ι → ℂ => fun i : S => w i * z i) ⁻¹' U) := by
  have hpos : 0 < ((Measure.pi (fun _ : S => complexGaussian v)).map
      (fun z : S → ℂ => fun i => w i * z i)) U := by
    let := weighted_finite_complexGaussian_isOpenPosMeasure hv w hw
    exact hU.measure_pos _ hne
  rw [← weighted_gaussian_head_law S v w, Measure.map_apply (by fun_prop) hU.measurableSet] at hpos
  exact hpos

end DefocusingNLS

end OAI
