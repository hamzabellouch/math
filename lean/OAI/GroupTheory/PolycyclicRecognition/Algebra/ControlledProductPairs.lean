import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledMetricFolner
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Controlled Følner pairs from compact product coordinates

The required estimate is an explicit right-product containment in a larger
rectangle, together with a bounded ratio of the two coordinate volumes.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set Filter
open scoped ENNReal

variable {G N D : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace N] [TopologicalSpace D] [T2Space N] [T2Space D]
  [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
  [SecondCountableTopology N] [SecondCountableTopology D]
  (e : G ≃ₜ N × D) (μN : Measure N) (μD : Measure D)
  [SFinite μN] [SFinite μD] [IsFiniteMeasureOnCompacts μN] [IsFiniteMeasureOnCompacts μD]

omit [Group G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [T2Space N] [T2Space D] [SFinite μN] [IsFiniteMeasureOnCompacts μN]
  [IsFiniteMeasureOnCompacts μD] [SecondCountableTopology N] in
theorem productCoordinateMeasure_rectangle {A : Set N} {B : Set D}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.map e.symm (μN.prod μD)) (e ⁻¹' (A ×ˢ B)) = μN A * μD B := by
  rw [Measure.map_apply e.symm.measurable (e.measurable (hA.prod hB))]
  have he : e.symm ⁻¹' (e ⁻¹' (A ×ˢ B)) = A ×ˢ B := by
    ext p
    simp only [mem_preimage, e.apply_symm_apply]
  rw [he, Measure.prod_prod]

def controlledMetricFolnerPairs_of_product_sets
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n) (hlim : Tendsto scale atTop atTop)
    (A A' : ℕ → Set N) (B B' : ℕ → Set D)
    (hA : ∀ n, IsCompact (A n)) (hA' : ∀ n, IsCompact (A' n))
    (hB : ∀ n, IsCompact (B n)) (hB' : ∀ n, IsCompact (B' n))
    (hneA : ∀ n, (A n).Nonempty) (hneB : ∀ n, (B n).Nonempty)
    (hposA : ∀ n, 0 < μN.real (A n)) (hposB : ∀ n, 0 < μD.real (B n))
    {R CN CD : ℝ} (hR : 0 ≤ R) (hCN : 0 ≤ CN) (hCD : 0 ≤ CD)
    (hrad : ∀ n x, e x ∈ A n ×ˢ B n → dist 1 x ≤ R * scale n)
    (hmul : ∀ n x, e x ∈ A n ×ˢ B n → ∀ y, dist 1 y ≤ 2 * scale n →
      e (x * y) ∈ A' n ×ˢ B' n)
    (hvolA : ∀ n, μN.real (A' n) ≤ CN * μN.real (A n))
    (hvolB : ∀ n, μD.real (B' n) ≤ CD * μD.real (B n)) :
    ControlledMetricFolnerPairs (Measure.map e.symm (μN.prod μD)) := by
  let μ := Measure.map e.symm (μN.prod μD)
  let S := fun n => e ⁻¹' (A n ×ˢ B n)
  have hc (n : ℕ) : IsCompact (S n) := e.isCompact_preimage.mpr ((hA n).prod (hB n))
  have hn (n : ℕ) : (S n).Nonempty := by
    obtain ⟨a, ha⟩ := hneA n
    obtain ⟨b, hb⟩ := hneB n
    refine ⟨e.symm (a, b), ?_⟩
    change e (e.symm (a, b)) ∈ A n ×ˢ B n
    rw [e.apply_symm_apply]
    exact ⟨ha, hb⟩
  have heq (n : ℕ) : μ.real (S n) = μN.real (A n) * μD.real (B n) := by
    rw [measureReal_def, productCoordinateMeasure_rectangle e μN μD
      (hA n).measurableSet (hB n).measurableSet, ENNReal.toReal_mul]
    rfl
  refine {
    scale := scale, scale_pos := hscale, scale_tendsto := hlim,
    sets := S, compact := hc, nonempty := hn,
    positive := fun n => (heq n).symm ▸ mul_pos (hposA n) (hposB n),
    radiusConstant := R, radius_nonneg := hR, radius_bound := hrad,
    volumeConstant := CN * CD, volume_nonneg := mul_nonneg hCN hCD,
    volume_bound := ?_ }
  intro n
  have hs0 := (hscale n).le
  have hsub : cthickening (2 * scale n) (S n) ⊆ e ⁻¹' (A' n ×ˢ B' n) := by
    intro z hz
    have hi : infDist z (S n) ≤ 2 * scale n := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hz
      simpa only [infDist, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * scale n)] using h
    obtain ⟨x, hx, hdist⟩ := (hc n).exists_infDist_eq_dist (hn n) z
    have hxy : dist 1 (x⁻¹ * z) ≤ 2 * scale n := by
      have he : dist 1 (x⁻¹ * z) = dist z x := by
        simpa only [mul_one, mul_inv_cancel_left, dist_comm] using
          (dist_mul_left x (1 : G) (x⁻¹ * z)).symm
      rw [he, ← hdist]
      exact hi
    have h := hmul n x hx (x⁻¹ * z) hxy
    change e z ∈ A' n ×ˢ B' n
    simpa only [mul_inv_cancel_left] using h
  have hf : μ (e ⁻¹' (A' n ×ˢ B' n)) ≠ ∞ := by
    rw [productCoordinateMeasure_rectangle e μN μD (hA' n).measurableSet (hB' n).measurableSet]
    exact ENNReal.mul_ne_top (hA' n).measure_ne_top (hB' n).measure_ne_top
  have hm := ENNReal.toReal_mono hf (measure_mono (μ := μ) hsub)
  rw [productCoordinateMeasure_rectangle e μN μD (hA' n).measurableSet (hB' n).measurableSet,
    ENNReal.toReal_mul] at hm
  rw [heq]
  exact hm.trans ((mul_le_mul (hvolA n) (hvolB n) (measureReal_nonneg)
    (mul_nonneg hCN measureReal_nonneg)).trans_eq (by ring))

end PolycyclicRecognition

end

end OAI
