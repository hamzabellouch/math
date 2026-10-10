import OAI.Analysis.CircleDomains.Sobolev.ScalarFlattening
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! Coordinatewise scalar Lipschitz changes preserve null planar trace
pairs, including the constructed countable-value flattenings. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem lipschitz_plane_image_null {A : ℝ × ℝ → ℝ × ℝ} {L : ℝ≥0}
    (hA : LipschitzWith L A) {S : Set (ℝ × ℝ)} (hS : volume S = 0) :
    volume (A '' S) = 0 := by
  have h := hA.hausdorffMeasure_image_le (d := 2) (by norm_num) S
  simpa only [hausdorffMeasure_prod_real, hS, mul_zero, nonpos_iff_eq_zero] using h

 theorem coordinate_lipschitz_pair_null {X : Type*} {S : Set X} {u v : X → ℝ}
    (hz : volume ((fun x => (u x, v x)) '' S) = 0)
    {A B : ℝ → ℝ} {L M : ℝ≥0} (hA : LipschitzWith L A) (hB : LipschitzWith M B) :
    volume ((fun x => (A (u x), B (v x))) '' S) = 0 := by
  have hmap : LipschitzWith (max (L*1) (M*1))
      (fun p : ℝ × ℝ => (A p.1, B p.2)) :=
    (hA.comp LipschitzWith.prod_fst).prodMk (hB.comp LipschitzWith.prod_snd)
  have he : (fun x => (A (u x), B (v x))) '' S =
      (fun p : ℝ × ℝ => (A p.1, B p.2)) '' ((fun x => (u x, v x)) '' S) := by
    rw [image_image]
  rw [he]
  exact lipschitz_plane_image_null hmap hz

 theorem flattened_pair_null {X : Type*} {S : Set X} {u v : X → ℝ}
    (hz : volume ((fun x => (u x, v x)) '' S) = 0)
    {O P : Set ℝ} (hO : MeasurableSet O) (hP : MeasurableSet P) :
    volume ((fun x => (flattenValues O (u x), flattenValues P (v x))) '' S) = 0 :=
  coordinate_lipschitz_pair_null hz (flattenValues_lipschitz hO) (flattenValues_lipschitz hP)

end CircleDomainRigidity

end

end OAI
