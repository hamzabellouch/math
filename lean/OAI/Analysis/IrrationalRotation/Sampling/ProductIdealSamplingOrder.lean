import OAI.Analysis.IrrationalRotation.Sampling.ProductIdealSamplingLimit
import OAI.Analysis.IrrationalRotation.Analysis.TriangularLawMass

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Invariant233.ProductModel.IdealSampling

theorem displacement_bounds (x z : Circle) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ h * ScalarSampling.delta (circleRepresentative x) * circleRepresentative z ∧
      h * ScalarSampling.delta (circleRepresentative x) * circleRepresentative z ≤ h / 2 := by
  have hx := Sampling.representative_mem_Ico x
  have hz := Sampling.representative_mem_Ico z
  have hd : 0 ≤ ScalarSampling.delta (circleRepresentative x) :=
    le_min hx.1 (sub_nonneg.mpr hx.2.le)
  have hdhalf : ScalarSampling.delta (circleRepresentative x) ≤ 1 / 2 := by
    have ha := min_le_left (circleRepresentative x) (1 - circleRepresentative x)
    have hb := min_le_right (circleRepresentative x) (1 - circleRepresentative x)
    dsimp [ScalarSampling.delta]
    linarith
  constructor
  · exact mul_nonneg (mul_nonneg hh hd) hz.1
  · calc
      h * ScalarSampling.delta (circleRepresentative x) * circleRepresentative z ≤
          h * ScalarSampling.delta (circleRepresentative x) * 1 :=
        mul_le_mul_of_nonneg_left hz.2.le (mul_nonneg hh hd)
      _ ≤ h / 2 := by nlinarith

theorem representative_displaced (x z : Circle) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1) :
    circleRepresentative (x + ((h * ScalarSampling.delta (circleRepresentative x) *
      circleRepresentative z : ℝ) : Circle)) =
      circleRepresentative x + h * ScalarSampling.delta (circleRepresentative x) *
        circleRepresentative z := by
  have hx := Sampling.representative_mem_Ico x
  have hz := Sampling.representative_mem_Ico z
  have hd : 0 ≤ ScalarSampling.delta (circleRepresentative x) :=
    le_min hx.1 (sub_nonneg.mpr hx.2.le)
  have hdb : ScalarSampling.delta (circleRepresentative x) ≤ 1 - circleRepresentative x :=
    min_le_right _ _
  have hbound : h * ScalarSampling.delta (circleRepresentative x) * circleRepresentative z ≤
      h * (1 - circleRepresentative x) := by
    calc
      _ ≤ h * ScalarSampling.delta (circleRepresentative x) * 1 :=
        mul_le_mul_of_nonneg_left hz.2.le (mul_nonneg hh0 hd)
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hdb hh0
  have hlo := (displacement_bounds x z hh0).1
  change ProductCocycle.representative _ = _
  rw [ProductCocycle.representative_add]
  apply Int.fract_eq_self.mpr
  change 0 ≤ circleRepresentative x + _ ∧ circleRepresentative x + _ < 1
  constructor
  · linarith [hx.1]
  · have hp := mul_pos (sub_pos.mpr hh1) (sub_pos.mpr hx.2)
    nlinarith

theorem endpoint_ordered (I D : Finset ℕ) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1)
    (xz : EndpointPair) (htri : xz ∈ triangularEvent I) :
    Ordered xz.1 (endpoint I D h xz.1 xz.2) := by
  intro i
  by_cases hi : i ∈ I
  · simpa [endpoint, hi] using (htri i hi).le
  · by_cases hd : i ∈ D
    · simp only [endpoint, hi, hd, ite_false, ite_true]
      rw [representative_displaced _ _ hh0 hh1]
      exact le_add_of_nonneg_right (displacement_bounds _ _ hh0).1
    · simp [endpoint, hi, hd]

theorem uncutLaw_ordered (I D : Finset ℕ) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1) :
    ∀ᵐ xy ∂uncutLaw I D h, Ordered xy.1 xy.2 := by
  rw [uncutLaw, ae_map_iff (endpointMap_measurable I D h).aemeasurable
    Sampling.ordered_measurable]
  filter_upwards [ae_restrict_mem (Sampling.triangularEvent_measurable I)] with xz hxz
  exact endpoint_ordered I D hh0 hh1 xz hxz

theorem law_le_uncutLaw (I D : Finset ℕ) (h α : ℝ) : law I D h α ≤ uncutLaw I D h :=
  Measure.map_mono Measure.restrict_le_self (endpointMap_measurable I D h)

theorem law_ordered (I D : Finset ℕ) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1) (α : ℝ) :
    ∀ᵐ xy ∂law I D h α, Ordered xy.1 xy.2 :=
  (uncutLaw_ordered I D hh0 hh1).filter_mono (ae_mono (law_le_uncutLaw I D h α))

theorem uncutLaw_mass (I D : Finset ℕ) (h : ℝ) :
    uncutLaw I D h univ = (1 / 2 : ℝ≥0∞) ^ I.card := by
  rw [uncutLaw, Measure.map_apply (endpointMap_measurable I D h) MeasurableSet.univ,
    preimage_univ, sourceMeasure, Measure.restrict_apply_univ]
  exact triangularEvent_mass I

end Invariant233.ProductModel.IdealSampling

end

end OAI
