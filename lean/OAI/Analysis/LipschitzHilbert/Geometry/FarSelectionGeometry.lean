import OAI.Analysis.LipschitzHilbert.Estimates.MaximalContainmentExclusion
import OAI.Analysis.LipschitzHilbert.Geometry.UniformNearSelection

namespace OAI

/-! Geometric consequences of actual maximal non-removal for far pairs.
In particular, both widths are small relative to the angle and all
remaining angles satisfy the bound needed for popularity projection. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

namespace Rectangle

theorem dilate_carrier_mono (R : Rectangle) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    (R.dilate a ha).carrier ⊆ (R.dilate b hb).carrier := by
  intro x hx
  change |R.axes.repr (x-R.center) 0| ≤ a*R.long/2 ∧ |R.axes.repr (x-R.center) 1| ≤ a*R.short/2 at hx
  constructor
  · change |R.axes.repr (x-R.center) 0| ≤ b*R.long/2
    have hl := mul_le_mul_of_nonneg_right hab R.long_pos.le
    exact hx.1.trans (by linarith)
  · change |R.axes.repr (x-R.center) 1| ≤ b*R.short/2
    have hl := mul_le_mul_of_nonneg_right hab R.short_pos.le
    exact hx.2.trans (by linarith)

end Rectangle

theorem selectionThreshold_small : 36*selectionThreshold < 1 := by
  change (36:ℝ≥0∞)*ENNReal.ofReal (1/1048576:ℝ) < 1
  rw [show (36:ℝ≥0∞)=ENNReal.ofReal 36 by norm_num,←ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_lt_one]
  norm_num

theorem far_selected_earlier_width {ι κ : Type*} [Fintype κ]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle) (previous : Finset ι)
    (s r : ι) (hs : s ∈ previous) (hL : (R r).long ≤ (R s).long)
    (hinter : ((R s).carrier ∩ (R r).carrier).Nonempty)
    (hfar : 64*(R r).short < (R r).long * dist ((R s).axes 0) ((R r).axes 0))
    (hnot : ¬maximalBlocked e R selectionDilation (by norm_num) selectionThreshold previous r) :
    32*(R s).short < dist ((R s).axes 0) ((R r).axes 0)*(R s).long := by
  by_contra hn
  have hwidth : dist ((R s).axes 0) ((R r).axes 0)*(R s).long ≤ 32*(R s).short := le_of_not_gt hn
  have hangle : (R r).long * dist ((R s).axes 0) ((R r).axes 0) ≤ 32*(R s).short := by
    have h := mul_le_mul_of_nonneg_left hL (dist_nonneg (x := (R s).axes 0) (y := (R r).axes 0))
    nlinarith
  have hshort : (R r).short ≤ (R s).short := by linarith [(R r).short_pos]
  have hc := Rectangle.controlled_angle_containment (R s) (R r) 32 (by norm_num) hL hshort hangle hinter
  have hsub : (R r).carrier ⊆ ((R s).dilate (selectionDilation/2) (by norm_num)).carrier :=
    hc.trans ((R s).dilate_carrier_mono (2*32+5) (selectionDilation/2) (by norm_num) (by norm_num) (by norm_num))
  exact (unblocked_not_contained_in_earlier_dilation e R selectionDilation (by norm_num)
    selectionThreshold selectionThreshold_small previous s r hs hnot) hsub

theorem far_selected_angle_bound (S T : Rectangle) {v : Plane → Plane} {K δ : ℝ≥0}
    (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1) (hδ : 0 < δ)
    (hS : S.Admissible v K δ) (hT : T.Admissible v K δ)
    (hL : T.long ≤ S.long) (hinter : (S.carrier ∩ T.carrier).Nonempty)
    (hfar : 64*T.short < T.long*dist (S.axes 0) (T.axes 0))
    (hwidth : 32*S.short < dist (S.axes 0) (T.axes 0)*S.long) :
    dist (S.axes 0) (T.axes 0) ≤ 5*(K:ℝ)*S.long ∧ dist (S.axes 0) (T.axes 0) ≤ 1/20 := by
  let θ := dist (S.axes 0) (T.axes 0)
  have hST : S.short/(2*S.long) ≤ θ/64 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) S.long_pos)).mpr
    dsimp [θ]
    nlinarith
  have hTT : T.short/(2*T.long) ≤ θ/128 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) T.long_pos)).mpr
    dsimp [θ]
    nlinarith
  have hraw := S.intersecting_axes_distance T hv hu hδ hS hT hinter
  have hK := mul_le_mul_of_nonneg_left hL K.coe_nonneg
  have hKnonneg : 0 ≤ (K:ℝ)*S.long := mul_nonneg K.coe_nonneg S.long_pos.le
  have hbound : θ ≤ 5*(K:ℝ)*S.long := by
    dsimp [θ] at hST hTT ⊢
    nlinarith
  refine ⟨hbound,?_⟩
  have hscale := hS.1
  change 100*(K:ℝ)*S.long ≤ 1 at hscale
  nlinarith

/-- Non-removal controls the reference width by the *later* length as
well. This is the local scale bound used in the strip estimates. -/
theorem far_selected_reference_width {ι κ : Type*} [Fintype κ]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle) (previous : Finset ι)
    (s r : ι) (hs : s ∈ previous) (hL : (R r).long ≤ (R s).long)
    (hinter : ((R s).carrier ∩ (R r).carrier).Nonempty)
    (hfar : 64*(R r).short < (R r).long * dist ((R s).axes 0) ((R r).axes 0))
    (hnot : ¬maximalBlocked e R selectionDilation (by norm_num) selectionThreshold previous r) :
    32*(R s).short < (R r).long*dist ((R s).axes 0) ((R r).axes 0) := by
  by_contra hn
  have hangle : (R r).long*dist ((R s).axes 0) ((R r).axes 0) ≤ 32*(R s).short :=
    le_of_not_gt hn
  have hshort : (R r).short ≤ (R s).short := by linarith [(R r).short_pos]
  have hc := Rectangle.controlled_angle_containment (R s) (R r) 32 (by norm_num)
    hL hshort hangle hinter
  have hsub : (R r).carrier ⊆ ((R s).dilate (selectionDilation/2) (by norm_num)).carrier :=
    hc.trans ((R s).dilate_carrier_mono (2*32+5) (selectionDilation/2)
      (by norm_num) (by norm_num) (by norm_num))
  exact (unblocked_not_contained_in_earlier_dilation e R selectionDilation (by norm_num)
    selectionThreshold selectionThreshold_small previous s r hs hnot) hsub

end LipschitzHilbert

end

end OAI
