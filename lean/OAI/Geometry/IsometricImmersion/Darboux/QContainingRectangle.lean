import OAI.Geometry.IsometricImmersion.Darboux.QEnergyApplication
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

private theorem real_near_closed_interval {a b e x : ℝ} (hab : a ≤ b)
    (he : 0 < e) (hx : x ∈ Ioo (a-e) (b+e)) :
    ∃ y ∈ Icc a b, |x-y| < e := by
  by_cases hxa : x < a
  · refine ⟨a,⟨le_rfl,hab⟩,?_⟩
    rw [abs_of_neg (sub_neg.mpr hxa)]
    linarith [hx.1]
  by_cases hbx : b < x
  · refine ⟨b,⟨hab,le_rfl⟩,?_⟩
    rw [abs_of_pos (sub_pos.mpr hbx)]
    linarith [hx.2]
  exact ⟨x,⟨le_of_not_gt hxa,le_of_not_gt hbx⟩,by simpa using he⟩

theorem closedRectangle_compact (l r a b : ℝ) : IsCompact (closedRectangle l r a b) := by
  have he : closedRectangle l r a b = Icc (![l,a] : Coord) ![r,b] := by
    ext p
    constructor
    · intro hp
      constructor
      · intro i
        fin_cases i
        · exact hp.1.1
        · exact hp.2.1
      · intro i
        fin_cases i
        · exact hp.1.2
        · exact hp.2.2
    · intro hp
      exact ⟨⟨hp.1 0,hp.2 0⟩,⟨hp.1 1,hp.2 1⟩⟩
  rw [he]
  exact isCompact_Icc

theorem exists_containing_coordinateRectangle {U : Set Coord} (hU : IsOpen U)
    {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b)
    (hbox : closedRectangle (-R) R a b ⊆ U) :
    ∃ radius lo hi : ℝ, R < radius ∧ lo < a ∧ b < hi ∧
      coordinateRectangle radius lo hi ⊆ U := by
  obtain ⟨e,he,hthick⟩ := (closedRectangle_compact (-R) R a b).exists_thickening_subset_open hU hbox
  refine ⟨R+e,a-e,b+e,by linarith,by linarith,by linarith,?_⟩
  intro p hp
  obtain ⟨x,hx,hxe⟩ := real_near_closed_interval (show -R ≤ R by linarith) he
    (show p 0 ∈ Ioo (-R-e) (R+e) by
      exact ⟨by linarith [hp.1.1],hp.1.2⟩)
  obtain ⟨t,ht,hte⟩ := real_near_closed_interval hab he hp.2
  apply hthick
  rw [Metric.mem_thickening_iff]
  refine ⟨![x,t],⟨hx,ht⟩,?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_lt_iff he).mpr
  intro i
  fin_cases i
  · change ‖p 0-x‖ < e
    simpa only [Real.norm_eq_abs] using hxe
  · change ‖p 1-t‖ < e
    simpa only [Real.norm_eq_abs] using hte

theorem exists_actual_Q_containing_rectangle
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b)
    (hbox : closedRectangle (-R) R a b ⊆ U)
    (hxx : ∀ p ∈ closedRectangle (-R) R a b, covHessian g z p 0 0 ≠ 0) :
    ∃ radius lo hi : ℝ, R < radius ∧ lo < a ∧ b < hi ∧
      coordinateRectangle radius lo hi ⊆ U ∧
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) := by
  let V := U ∩ (fun p => covHessian g z p 0 0) ⁻¹' ({0}ᶜ : Set ℝ)
  have hV : IsOpen V := (covHessian_contDiffOn hg hU hz 0 0).continuousOn.isOpen_inter_preimage hU
    isClosed_singleton.isOpen_compl
  have hsub : closedRectangle (-R) R a b ⊆ V := by
    intro p hp
    exact ⟨hbox hp,hxx p hp⟩
  obtain ⟨radius,lo,hi,hr,hl,hh,hVU⟩ := exists_containing_coordinateRectangle hV hR hab hsub
  exact ⟨radius,lo,hi,hr,hl,hh,fun p hp => (hVU hp).1,fun p hp => (hVU hp).2⟩

end SmoothLocal.HighEquation

end

end OAI
