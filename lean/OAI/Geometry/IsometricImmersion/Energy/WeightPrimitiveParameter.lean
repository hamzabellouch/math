import OAI.Geometry.IsometricImmersion.Calculus.FinitePrimitive

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Flow

variable {B : Coord → ℝ} {R a b : ℝ}

theorem coefficient_pair_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (pairRectangle R a b) := by
  have hpoint : ContDiff ℝ ∞ (fun p : ℝ × ℝ => coordinatePoint p.1 p.2) := by
    unfold coordinatePoint
    fun_prop
  exact hB.comp hpoint.contDiffOn (fun p hp => point_mem_rectangle hp.1 hp.2)

theorem coefficient_pairPartialY
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    {x y : ℝ} (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    pairPartialY (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y) =
      coordPartial 1 B (coordinatePoint x y) := by
  have hdB : DifferentiableAt ℝ B (coordinatePoint x y) :=
    ((hB.contDiffAt ((coordinateRectangle_isOpen R a b).mem_nhds
      (point_mem_rectangle hx hy))).differentiableAt (by simp))
  have hdPair : DifferentiableAt ℝ (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y) :=
    (((coefficient_pair_contDiffOn hB).contDiffAt
      ((pairRectangle_isOpen R a b).mem_nhds ⟨hx, hy⟩)).differentiableAt (by simp))
  have hcoord : HasDerivAt (fun t => B (coordinatePoint x t))
      (coordPartial 1 B (coordinatePoint x y)) y :=
    hdB.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)
  have hpair : HasDerivAt (fun t => B (coordinatePoint x t))
      (pairPartialY (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y)) y :=
    hdPair.hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  exact hpair.unique hcoord

theorem coordinatePrimitive_partial_s
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    coordPartial 1 (coordinatePrimitive B) p =
      ∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1)) := by
  have hpairC1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => B (coordinatePoint q.1 q.2))
      (pairRectangle R a b) := (coefficient_pair_contDiffOn hB).of_le (by simp)
  have hftc := pairPrimitive_hasDerivAt_y hpairC1 hp.1 hp.2
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have he : pairPrimitive
      (pairPartialY (fun q : ℝ × ℝ => B (coordinatePoint q.1 q.2))) (p 0, p 1) =
      ∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1)) := by
    unfold pairPrimitive
    apply intervalIntegral.integral_congr
    intro t ht
    exact coefficient_pairPartialY hB (hseg ht) hp.2
  rw [he] at hftc
  have hftc' : HasDerivAt (fun s => coordinatePrimitive B (coordinatePoint (p 0) s))
      (∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1))) (p 1) := by
    simpa [pairPrimitive, coordinatePrimitive, coordinatePoint] using hftc
  have hdI : DifferentiableAt ℝ (coordinatePrimitive B) (coordinatePoint (p 0) (p 1)) := by
    rw [point_eta]
    exact ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by simp)
  have hchain := hdI.hasFDerivAt.comp_hasDerivAt (p 1) (coordinatePoint_hasDerivAt_y (p 0) (p 1))
  have hcoord : HasDerivAt (fun s => coordinatePrimitive B (coordinatePoint (p 0) s))
      (coordPartial 1 (coordinatePrimitive B) p) (p 1) := by
    simpa only [point_eta, Function.comp_def, coordPartial] using hchain
  exact hcoord.unique hftc'

theorem coordinatePrimitive_segment_intervalIntegrable
    (hB : ContinuousOn B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    IntervalIntegrable (fun t => B (coordinatePoint t (p 1))) volume 0 (p 0) := by
  have hc : ContinuousOn (fun t => B (coordinatePoint t (p 1))) (Ioo (-R) R) :=
    hB.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => point_mem_rectangle ht hp.2)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  exact (hc.mono hseg).intervalIntegrable

theorem coordinatePrimitive_abs_bound
    (hB : ContinuousOn B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    {M : ℝ} (hbound : ∀ q ∈ coordinateRectangle R a b, |B q| ≤ M) :
    |coordinatePrimitive B p| ≤ R * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound p hp)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have hi := coordinatePrimitive_segment_intervalIntegrable hB hR hp
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := p 0) (C := M)
    (f := fun t => B (coordinatePoint t (p 1)))
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact hbound _ (point_mem_rectangle (hseg (uIoc_subset_uIcc ht)) hp.2))
  calc
    _ ≤ M * |p 0| := by simpa only [coordinatePrimitive, Real.norm_eq_abs, sub_zero] using hb
    _ ≤ M * R := mul_le_mul_of_nonneg_left (abs_lt.mpr hp.1).le hM
    _ = R * M := mul_comm _ _

theorem coordinatePrimitive_partial_s_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    {M : ℝ} (hBs : ∀ q ∈ coordinateRectangle R a b, |coordPartial 1 B q| ≤ M) :
    |coordPartial 1 (coordinatePrimitive B) p| ≤ R * M := by
  rw [coordinatePrimitive_partial_s hB hR hp]
  exact coordinatePrimitive_abs_bound
    (partial_contDiffOn hB (coordinateRectangle_isOpen R a b) 1).continuousOn hR hp hBs

end SmoothLocal.Weighted

end

end OAI
