import OAI.Analysis.CircleDomains.Reflection.RegularJordanBoundaryChart
import OAI.Analysis.CircleDomains.Topology.PlanarMapChangeVariables

namespace OAI

/-! Compact normal-coordinate rectangles retain the full Jordan boundary
and have positive actual Jacobian throughout. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma continuous_planarMapJacobian {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p => planarMapJacobian (fderiv ℝ F p)) := by
  have hd := hF.continuous_fderiv (by simp)
  have h1 := hd.clm_apply (continuous_const (y := (1,0)))
  have h2 := hd.clm_apply (continuous_const (y := (0,1)))
  exact ((Complex.continuous_re.comp h1).mul (Complex.continuous_im.comp h2)).sub
    ((Complex.continuous_im.comp h1).mul (Complex.continuous_re.comp h2))

lemma exists_regular_jordan_normal_box
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (r : ℝ), 0 < r ∧ r < 1/4 ∧
      (∀ p, e p = curveNormalStrip γ p) ∧ ContDiff ℝ ∞ e ∧
      Icc (t-r,-r) (t+r,r) ⊆ e.source ∧
      (∀ p ∈ Icc (t-r,-r) (t+r,r),
        e p ∈ frontier (jordanInterior H) ↔ p.2 = 0) ∧
      (∀ p ∈ Icc (t-r,-r) (t+r,r), 0 < planarMapJacobian (fderiv ℝ e p)) := by
  obtain ⟨e,U,ht,he,hs,_,hU,htU,_,hstraight⟩ :=
    exists_regular_jordan_boundary_chart hγ t
  have hval : e (t,0) = γ t := by simp [he,curveNormalStrip]
  have hj : 0 < planarMapJacobian (fderiv ℝ e (t,0)) := by
    have hfe : (e : (ℝ × ℝ) → ℂ) = curveNormalStrip γ := funext he
    rw [hfe]
    change 0 < _
    rw [show planarMapJacobian (fderiv ℝ (curveNormalStrip γ) (t,0)) =
      ‖deriv γ t‖^2 from curveNormalStrip_jacobian hγ.smooth t]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hγ.regular t))
  let V := (e.source ∩ e ⁻¹' U) ∩ {p | 0 < planarMapJacobian (fderiv ℝ e p)}
  have hV : IsOpen V := (e.open_source.inter (hU.preimage hs.continuous)).inter
    (isOpen_lt continuous_const (continuous_planarMapJacobian hs))
  have htV : (t,0) ∈ V := ⟨⟨ht,by simpa [hval] using htU⟩,hj⟩
  obtain ⟨δ,hδ,hδV⟩ := Metric.isOpen_iff.mp hV (t,0) htV
  let r : ℝ := min (δ/2) (1/8)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hsub : Icc (t-r,-r) (t+r,r) ⊆ V := by
    intro p hp
    apply hδV
    rw [mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,Real.dist_eq,sub_zero]
    have h1 : |p.1-t| ≤ r := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.2.1]⟩
    have h2 : |p.2| ≤ r := abs_le.mpr ⟨hp.1.2,hp.2.2⟩
    exact ⟨h1.trans_lt hrδ,h2.trans_lt hrδ⟩
  refine ⟨e,r,hr,(min_le_right _ _).trans_lt (by norm_num),he,hs,
    fun p hp => (hsub hp).1.1,?_,fun p hp => (hsub hp).2⟩
  intro p hp
  have h := hstraight (e p) (hsub hp).1.2
  rwa [e.left_inv (hsub hp).1.1] at h

end CircleDomainRigidity

end

end OAI
