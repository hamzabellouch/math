import OAI.Geometry.SurfaceImmersion.Atlas.CenteredParabolicChart

namespace OAI

/-! The phase-chart radius is fixed before choosing the independent phase
parameters and the centers. This resolves that order in finite preparation. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma abs_phaseLinear_le (ell v : Base) : |phaseLinear ell v| ≤ 2*‖ell‖*‖v‖ := by
  calc
    _ ≤ |ell.1*v.1|+|ell.2*v.2| := abs_add_le _ _
    _ = |ell.1| * |v.1| + |ell.2| * |v.2| := by rw [abs_mul,abs_mul]
    _ ≤ ‖ell‖*‖v‖+‖ell‖*‖v‖ := by
      gcongr
      · exact norm_fst_le ell
      · exact norm_fst_le v
      · exact norm_snd_le ell
      · exact norm_snd_le v
    _ = _ := by ring

theorem compact_uniform_centered_charts {P : Set Base} (hP : IsCompact P)
    (hP0 : ∀ ell ∈ P, ell ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∃ r : ℝ, 0 < r ∧ ∀ ell ∈ P, ∀ c : Base,
      ∃ e : OpenPartialHomeomorph Base Base,
        (∀ x, (e x).1 = centeredConvexPhase ell L c x) ∧
        ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
        closedBall c r ⊆ e.source := by
  have hA : Continuous (phaseCovectorSquare : Base → ℝ) := by
    unfold phaseCovectorSquare
    fun_prop
  obtain ⟨d,hd,hbound⟩ := hP.exists_forall_le' hA.continuousOn
    (fun ell hell => phaseCovectorSquare_pos (hP0 ell hell))
  obtain ⟨R₀,hR₀⟩ := hP.isBounded.subset_ball (0 : Base)
  let R := |R₀|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hnorm : ∀ ell ∈ P, ‖ell‖ ≤ R := by
    intro ell hell
    have hh := hR₀ hell
    rw [mem_ball,dist_zero_right] at hh
    exact hh.le.trans (by dsimp [R]; linarith [le_abs_self R₀])
  let r := d/(1+2*L*R)
  have hden : 0 < 1+2*L*R := by positivity
  have hr : 0 < r := div_pos hd hden
  have heq : (1+2*L*R)*r = d := by
    dsimp [r]
    field_simp
  have hsmall : L*(2*R*r) < d := by nlinarith
  refine ⟨r,hr,?_⟩
  intro ell hell c
  let e := centeredParabolicChart ell (hP0 ell hell) L hL.ne' c
  have hcover : closedBall c r ⊆ e.source := by
    intro x hx
    rw [mem_closedBall,dist_eq_norm] at hx
    apply (centeredParabolicChart_source ell (hP0 ell hell) L hL.ne' c x).mpr
    have hu : |phaseLinear ell (x-c)| ≤ 2*R*r :=
      (abs_phaseLinear_le ell (x-c)).trans (by gcongr; exact hnorm ell hell)
    have hlower := neg_le_of_abs_le hu
    have hb := hbound ell hell
    nlinarith
  obtain ⟨f,hfcover,hfe,_,_,hf,hfi⟩ := extend_compact_chart_inverse e
    (centeredParabolicChart_smooth ell (hP0 ell hell) L hL.ne' c)
    (centeredParabolicChart_inverse_smooth ell (hP0 ell hell) L hL.ne' c)
    (isCompact_closedBall c r) hcover
  exact ⟨f,fun x => by rw [hfe]; exact centeredParabolicChart_phase ell (hP0 ell hell) L hL.ne' c x,
    hf,hfi,hfcover⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
