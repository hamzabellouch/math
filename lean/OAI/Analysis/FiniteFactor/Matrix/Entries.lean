import OAI.Analysis.FiniteFactor.CrossedProduct.FiberTotal
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

abbrev sourceBaseMeasure : Measure (SourceCoordinate → ℝ) :=
  Measure.infinitePi (fun _ => unitIntervalMeasure)

/-- A product almost-everywhere identity holds on every integer fiber. -/
theorem source_ae_all_fibers {p : (SourceCoordinate → ℝ) × ℤ → Prop}
    (hp : ∀ᵐ z ∂sourceMeasure SourceCoordinate, p z) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ, p (x,n) := by
  exact (Measure.ae_ae_of_ae_prod hp).mono fun x hx => Measure.ae_count_iff.mp hx

/-- Constant coordinate vector, realized in the original source L2 space. -/
def sourceBasis (n : ℤ) : SourceHilbert SourceCoordinate :=
  sourceFiberIndicator Set.univ MeasurableSet.univ n

theorem sourceBasis_coe (n : ℤ) : sourceBasis n =ᵐ[sourceMeasure SourceCoordinate]
    fun z => if z.2 = n then 1 else 0 := by
  filter_upwards [sourceFiberIndicator_coe Set.univ MeasurableSet.univ n] with z hz
  rw [show (sourceBasis n) z = _ from hz]
  by_cases hn : z.2 = n <;> simp [hn]

theorem sourceBasis_zero : sourceBasis 0 = sourceVacuum := rfl

/-- Actual matrix coefficients obtained by applying H to constant e_n. -/
def sourceMatrixEntry (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (k n : ℤ) (x : SourceCoordinate → ℝ) : ℂ := (H (sourceBasis n)) (x,k)

theorem sourceScalar_apply_ae (g : SourceBaseFunction) (f : SourceHilbert SourceCoordinate) :
    sourceScalar g f =ᵐ[sourceMeasure SourceCoordinate] fun z => g.toFun z.1 * f z := by
  filter_upwards [sourcePi_apply_ae (fun _ => 0) g f, sourceHilbert_cube] with z hz hc
  change (sourcePi (fun _ => 0) g f) z = _
  rw [hz]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) z.2 z.1 = z.1 := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  simp [sourcePiSymbol, he]

theorem sourceScalar_indicator_basis (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (n : ℤ) : sourceScalar (sourceBaseIndicator A hA) (sourceBasis n) =
      sourceFiberIndicator A hA n := by
  apply Lp.ext
  filter_upwards [sourceScalar_apply_ae (sourceBaseIndicator A hA) (sourceBasis n),
    sourceBasis_coe n, sourceFiberIndicator_coe A hA n] with z hs hb hi
  rw [hs, hb, hi]
  by_cases ha : z.1 ∈ A <;> by_cases hn : z.2 = n <;> simp [sourceBaseIndicator, ha, hn]

/-- Localizing an input coordinate localizes every output coordinate by the
same base indicator. This uses the proved commutant of the actual algebra. -/
theorem sourceMatrixEntry_localize (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (n : ℤ) : ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      (H (sourceFiberIndicator A hA n)) (x,k) =
        A.indicator (sourceMatrixEntry H k n) x := by
  have he : H (sourceFiberIndicator A hA n) =
      sourceScalar (sourceBaseIndicator A hA) (H (sourceBasis n)) := by
    rw [← sourceScalar_indicator_basis]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate => T (sourceBasis n)) (sourceAlgebra_commutes_scalar θ hH
      (sourceBaseIndicator A hA))).symm
  rw [he]
  apply (source_ae_all_fibers (sourceScalar_apply_ae (sourceBaseIndicator A hA)
    (H (sourceBasis n)))).mono
  intro x hx k
  rw [hx]
  by_cases ha : x ∈ A <;> simp [sourceBaseIndicator, sourceMatrixEntry, ha]

end
end FiniteFactor

end OAI
