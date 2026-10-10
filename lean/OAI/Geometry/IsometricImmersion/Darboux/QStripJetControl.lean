import OAI.Geometry.IsometricImmersion.Darboux.QActualSegmentTransfer
import OAI.Geometry.IsometricImmersion.Energy.MultiplierIntegral
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem horizontal_partial_eq_of_slice_eq {f f0 : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : ContDiffOn ℝ ∞ f0 U) (hU : IsOpen U)
    {left right a : ℝ}
    (hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (heq : ∀ x ∈ Ioo left right, f0 (boxPoint x a) = f (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    coordPartial 0 f0 (boxPoint x a) = coordPartial 0 f (boxPoint x a) := by
  have hd : HasDerivAt (fun t => f (boxPoint t a)) (coordPartial 0 f (boxPoint x a)) x :=
    ((hf.contDiffAt (hU.mem_nhds (hline x hx))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      x (boxPoint_hasDerivAt_t x a)
  have hd0 : HasDerivAt (fun t => f0 (boxPoint t a)) (coordPartial 0 f0 (boxPoint x a)) x :=
    ((hf0.contDiffAt (hU.mem_nhds (hline x hx))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      x (boxPoint_hasDerivAt_t x a)
  have hev : (fun t => f0 (boxPoint t a)) =ᶠ[𝓝 x] (fun t => f (boxPoint t a)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact heq t ht
  rw [← hd0.deriv, ← hd.deriv]
  exact hev.deriv_eq

theorem qSolutionJet_eq_of_cauchy_data {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a : ℝ}
    (hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, z0 (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right,
      coordPartial 1 z0 (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    qSolutionJet z0 (boxPoint x a) = qSolutionJet z (boxPoint x a) := by
  have hxfirst : ∀ x ∈ Ioo left right,
      coordPartial 0 z0 (boxPoint x a) = coordPartial 0 z (boxPoint x a) :=
    fun x hx => horizontal_partial_eq_of_slice_eq hz hz0 hU hline hvalue hx
  have hxx := horizontal_partial_eq_of_slice_eq (partial_contDiffOn hz hU 0)
    (partial_contDiffOn hz0 hU 0) hU hline hxfirst hx
  have hxy := horizontal_partial_eq_of_slice_eq (partial_contDiffOn hz hU 1)
    (partial_contDiffOn hz0 hU 1) hU hline hvelocity hx
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hxfirst x hx
  · exact hvelocity x hx
  · exact hxy
  · exact hxx

theorem coordinate_word_vertical_variation {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Icc left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M : ℝ} (hB : CoordinateBound f (closedRectangle left right a b) 3 M)
    (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
    |iteratedCoordPartial ds f (boxPoint x t) -
      iteratedCoordPartial ds f (boxPoint x a)| ≤ M * |t - a| := by
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun y => iteratedCoordPartial ds f (boxPoint x y))
        (coordPartial 1 (iteratedCoordPartial ds f) (boxPoint x s)) s :=
    (LowQuotient.iterated_differentiableAt hf hU (hbox (boxPoint_mem hx hs)) ds).hasFDerivAt.comp_hasDerivAt
      s (boxPoint_hasDerivAt_s x s)
  have hb (s : ℝ) (hs : s ∈ Icc a b) :
      ‖deriv (fun y => iteratedCoordPartial ds f (boxPoint x y)) s‖ ≤ M := by
    rw [(hd s hs).deriv, Real.norm_eq_abs]
    exact hB (1 :: ds) (Nat.succ_le_succ hds) _ (boxPoint_mem hx hs)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hd s hs).differentiableAt) hb (show a ∈ Icc a b from ⟨le_rfl, hab⟩) ht

theorem coordinate_word_difference_on_strip {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Icc left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M M0 : ℝ} (hB : CoordinateBound z (closedRectangle left right a b) 3 M)
    (hB0 : CoordinateBound z0 (closedRectangle left right a b) 3 M0)
    (ds : List (Fin 2)) (hds : ds.length ≤ 2)
    (hinitial : iteratedCoordPartial ds z0 (boxPoint x a) =
      iteratedCoordPartial ds z (boxPoint x a)) :
    |iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x t)| ≤
      (M + M0) * |t - a| := by
  have h0 := coordinate_word_vertical_variation hz0 hU hbox hx hab ht hB0 ds hds
  have h1 := coordinate_word_vertical_variation hz hU hbox hx hab ht hB ds hds
  calc
    _ = |(iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z0 (boxPoint x a)) -
      (iteratedCoordPartial ds z (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x a))| := by
      rw [hinitial]
      congr 1
      ring
    _ ≤ |iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z0 (boxPoint x a)| +
      |iteratedCoordPartial ds z (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x a)| := abs_sub _ _
    _ ≤ M0 * |t - a| + M * |t - a| := add_le_add h0 h1
    _ = (M + M0) * |t - a| := by ring

theorem qSolutionJet_distance_on_same_strip {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Ioo left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M M0 : ℝ} (hM : 0 ≤ M) (hM0 : 0 ≤ M0)
    (hB : CoordinateBound z (closedRectangle left right a b) 3 M)
    (hB0 : CoordinateBound z0 (closedRectangle left right a b) 3 M0)
    (hvalue : ∀ x ∈ Ioo left right, z0 (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right,
      coordPartial 1 z0 (boxPoint x a) = coordPartial 1 z (boxPoint x a)) :
    ‖qSolutionJet z0 (boxPoint x t) - qSolutionJet z (boxPoint x t)‖ ≤
      (M + M0) * (b - a) := by
  have hx' : x ∈ Icc left right := ⟨hx.1.le, hx.2.le⟩
  have hinitial := qSolutionJet_eq_of_cauchy_data hz hz0 hU
    (fun y hy => hbox (boxPoint_mem ⟨hy.1.le, hy.2.le⟩ ⟨le_rfl, hab⟩)) hvalue hvelocity hx
  have hword (ds : List (Fin 2)) (hds : ds.length ≤ 2)
      (he : iteratedCoordPartial ds z0 (boxPoint x a) = iteratedCoordPartial ds z (boxPoint x a)) :
      |iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x t)| ≤
        (M + M0) * (b - a) := by
    apply (coordinate_word_difference_on_strip hz hz0 hU hbox hx' hab ht hB hB0 ds hds he).trans
    apply mul_le_mul_of_nonneg_left _ (add_nonneg hM hM0)
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    exact sub_le_sub_right ht.2 a
  apply state_distance_le_of_coordinate_error (mul_nonneg (add_nonneg hM hM0) (sub_nonneg.mpr hab))
  apply qSolutionJet_coordinate_error z z0 (boxPoint x t)
    (mul_nonneg (add_nonneg hM hM0) (sub_nonneg.mpr hab))
  · intro i
    fin_cases i
    · exact hword [0] (by norm_num) (congrFun hinitial 2)
    · exact hword [1] (by norm_num) (congrFun hinitial 3)
  · exact hword [0, 1] (by norm_num) (congrFun hinitial 4)
  · exact hword [0, 0] (by norm_num) (congrFun hinitial 5)

end SmoothLocal.HighEquation

end

end OAI
