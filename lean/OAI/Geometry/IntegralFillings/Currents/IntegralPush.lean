import Mathlib
import OAI.Geometry.IntegralFillings.Geometry.Comparison
import OAI.Geometry.IntegralFillings.Currents.PushBoundary
import OAI.Geometry.IntegralFillings.Charts.Postcompose

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory
open CurrentOperations

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X]

lemma integerRectifiable_push_of_bilipschitz {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {f : X → Y} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfJ : AntilipschitzWith J f) :
    IntegerRectifiable (pushCurrent f T) := by
  classical
  obtain ⟨C,hdis,hC,hm,heq⟩ := hT
  choose L U hL hU using fun i => (C i).bilipschitz
  let D : ℕ → IntegerChart Y k := fun i => (C i).postcompose hf (hfJ.comp (hU i))
  have hDaction (i : ℕ) : (D i).action = pushCurrent f (C i).action :=
    (C i).postcompose_action hf (hfJ.comp (hU i))
  have hD (i : ℕ) : IsMetricCurrent (D i).action := by
    rw [hDaction]
    exact pushCurrent_isMetricCurrent (hC i) hf
  refine ⟨D,?_,hD,?_,?_⟩
  · intro i j hij
    change Disjoint ((C i).postcompose hf _).image ((C j).postcompose hf _).image
    rw [(C i).postcompose_image,(C j).postcompose_image]
    exact (Set.disjoint_image_iff hfJ.injective).mpr (hdis hij)
  · apply (hm.mul_left ((K : ℝ)^k)).of_nonneg_of_le
    · intro i
      exact mass_nonneg (D i).action
    · intro i
      rw [hDaction]
      exact mass_pushCurrent_le (hC i) hf
  · intro b π
    by_cases h : Admissible b π
    · rw [pushCurrent_apply f T h,heq]
      exact tsum_congr (fun i => by rw [hDaction,pushCurrent_apply f (C i).action h])
    · rw [show pushCurrent f T b π = 0 from ite_eq_right h]
      symm
      calc
        (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
          tsum_congr (fun i => (hD i).offDomain b π h)
        _ = 0 := tsum_zero

lemma integral_push_of_bilipschitz {k : ℕ} {T : Functional X k}
    (hT : IsIntegral k T) {f : X → Y} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfJ : AntilipschitzWith J f) :
    IsIntegral k (pushCurrent f T) := by
  cases k with
  | zero => exact ⟨pushCurrent_isMetricCurrent hT.1 hf,
      integerRectifiable_push_of_bilipschitz hT.2 hf hfJ⟩
  | succ k =>
    refine ⟨pushCurrent_isMetricCurrent hT.1 hf,
      integerRectifiable_push_of_bilipschitz hT.2.1 hf hfJ,?_,?_⟩
    · rw [pushCurrent_boundarySucc T hf]
      exact pushCurrent_isMetricCurrent hT.2.2.1 hf
    · rw [pushCurrent_boundarySucc T hf]
      exact integerRectifiable_push_of_bilipschitz hT.2.2.2 hf hfJ

end SharpIntegralFillings
namespace SharpIntegralFillings
universe u
theorem IsCAT0.closedBall {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (o : X) {R : ℝ} (hR : 0 ≤ R) : IsCAT0 (Metric.closedBall o R) := by
  obtain ⟨s, hs, hd, hc⟩ := hX
  have hconv (x y : Metric.closedBall o R) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      s x.val y.val t ∈ Metric.closedBall o R := by
    have hh := hc x.val y.val o t 1 ht (by simp)
    rw [(hs x.val o).2] at hh
    have he : (t * dist x.val y.val - 1 * dist x.val o) ^ 2 +
          t * 1 * (dist y.val o ^ 2 - (dist x.val y.val - dist x.val o) ^ 2) =
        (1 - t) * dist x.val o ^ 2 + t * dist y.val o ^ 2 -
          t * (1 - t) * dist x.val y.val ^ 2 := by ring
    rw [he] at hh
    have hx := (sq_le_sq₀ dist_nonneg hR).mpr x.property
    have hy := (sq_le_sq₀ dist_nonneg hR).mpr y.property
    have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2)
    have hy' := mul_le_mul_of_nonneg_left hy ht.1
    have hh' : dist (s x.val y.val t) o ^ 2 ≤ R ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
        (sq_nonneg (dist x.val y.val))]
    exact (sq_le_sq₀ dist_nonneg hR).mp hh'
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclamp (t : ℝ) : clamp t ∈ Icc (0 : ℝ) 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclamp_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : clamp t = t := by
    simp only [clamp, min_eq_right ht.2, max_eq_right ht.1]
  let sB : Metric.closedBall o R → Metric.closedBall o R → ℝ →
      Metric.closedBall o R := fun x y t => ⟨s x.val y.val (clamp t), hconv x y _ (hclamp t)⟩
  refine ⟨sB, ?_, ?_, ?_⟩
  · intro x y
    constructor <;> apply Subtype.ext
    · change s x.val y.val (clamp 0) = x.val
      rw [hclamp_eq _ (by simp), (hs x.val y.val).1]
    · change s x.val y.val (clamp 1) = y.val
      rw [hclamp_eq _ (by simp), (hs x.val y.val).2]
  · intro x y u v hu hv
    change dist (s x.val y.val (clamp u)) (s x.val y.val (clamp v)) = _
    rw [hclamp_eq _ hu, hclamp_eq _ hv]
    exact hd x.val y.val u v hu hv
  · intro p x y u v hu hv
    change dist (s p.val x.val (clamp u)) (s p.val y.val (clamp v)) ^ 2 ≤ _
    rw [hclamp_eq _ hu, hclamp_eq _ hv]
    exact hc p.val x.val y.val u v hu hv

end SharpIntegralFillings

end

end OAI
