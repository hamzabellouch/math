import OAI.Analysis.FiniteFactor.CrossedProduct.RotationCommutant
import OAI.Analysis.FiniteFactor.CrossedProduct.VacuumFunctional

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Bounded measurable indicator on the base. -/
def sourceBaseIndicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    SourceBaseFunction where
  toFun := A.indicator (fun _ => (1 : ℂ))
  measurable := measurable_const.indicator hA
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by intro x _; by_cases hx : x ∈ A <;> simp [hx]

theorem sourceFiberMeasure_ne_top (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    sourceMeasure SourceCoordinate (A ×ˢ {n}) ≠ ∞ := by
  rw [Measure.prod_prod]
  simp

def sourceFiberIndicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    SourceHilbert SourceCoordinate :=
  indicatorConstLp 2 (hA.prod (measurableSet_singleton n)) (sourceFiberMeasure_ne_top A n) (1 : ℂ)

theorem sourceFiberIndicator_coe (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceFiberIndicator A hA n =ᵐ[sourceMeasure SourceCoordinate]
      (A ×ˢ {n}).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

theorem sourceVacuum_coe : sourceVacuum =ᵐ[sourceMeasure SourceCoordinate]
    (Set.univ ×ˢ {(0 : ℤ)}).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

/-- Every bounded base indicator on an arbitrary fiber is in the vacuum's
commutant orbit. No cyclicity or separating property is assumed. -/
theorem sourceFiberIndicator_eq_orbit (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceFiberIndicator A hA n = sourceScalar (sourceBaseIndicator A hA)
      (sourceCommutantRotation θ n sourceVacuum) := by
  apply Lp.ext
  have hv := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae sourceVacuum_coe
  filter_upwards [sourceFiberIndicator_coe A hA n, sourceHilbert_cube,
    sourcePi_apply_ae (fun _ => 0) (sourceBaseIndicator A hA)
      (sourceTransport θ n n sourceVacuum), sourceTransport_apply_ae θ n n sourceVacuum,
    hv] with z hi hc hs ht hv
  change (sourceFiberIndicator A hA n) z =
    (sourcePi (fun _ => 0) (sourceBaseIndicator A hA) (sourceTransport θ n n sourceVacuum)) z
  rw [hi,hs,ht,hv]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) z.2 z.1 = z.1 := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  unfold sourcePiSymbol
  rw [he]
  by_cases ha : z.1 ∈ A <;> by_cases hn : z.2 = n <;>
    simp [sourceBaseIndicator, sourceTransportIndex, ha, hn, sub_eq_zero]

end
end FiniteFactor

end OAI
