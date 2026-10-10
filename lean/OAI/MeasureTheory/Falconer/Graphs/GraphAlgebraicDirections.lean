import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalPhase
import OAI.MeasureTheory.Falconer.Graphs.GraphChartRegularity

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

noncomputable def graphNormalizedAxis (η : Plane) : Plane := ‖η‖⁻¹ • η

noncomputable def graphAlgebraicDirection (plus : Bool) (p : Plane × ℝ) : Plane :=
  (Real.sqrt (1+p.2^2))⁻¹ •
    (graphNormalizedAxis p.1 + (if plus then p.2 else -p.2) • quarterTurn (graphNormalizedAxis p.1))

theorem graphNormalizedAxis_contDiffAt (η : Plane) (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ graphNormalizedAxis η :=
  ((contDiffAt_id.norm ℝ hη).inv (norm_ne_zero_iff.mpr hη)).smul contDiffAt_id

theorem quarterTurn_contDiff : ContDiff ℝ ∞ quarterTurn := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Plane => -x 1)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Plane => x 0)
    fun_prop

theorem graphAlgebraicDirection_contDiffAt (plus : Bool) (p : Plane × ℝ) (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (graphAlgebraicDirection plus) p := by
  have ha : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => graphNormalizedAxis q.1) p :=
    (graphNormalizedAxis_contDiffAt p.1 hp).comp p contDiffAt_fst
  have hs : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => (Real.sqrt (1+q.2^2))⁻¹) p :=
    ((contDiffAt_const.add (contDiffAt_snd.pow 2)).sqrt (by positivity)).inv (by positivity)
  have hz : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => if plus then q.2 else -q.2) p := by
    cases plus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  exact hs.smul (ha.add (hz.smul (quarterTurn_contDiff.contDiffAt.comp p ha)))

theorem graphNormalizedAxis_eq {η : Plane} (hη : η ∈ graphPlaneSlit) :
    graphNormalizedAxis η = sourceDirection (graphPlaneAngle η) := by
  have hp := polarCoord.map_source hη
  have hn : 0 < ‖η‖ := by
    simpa only [graphPlaneEquiv_symm_radius, mem_Ioi] using hp.1
  calc
    graphNormalizedAxis η = ‖η‖⁻¹ • (‖η‖ • sourceDirection (graphPlaneAngle η)) :=
      congrArg (fun v : Plane => ‖η‖⁻¹ • v) (graph_plane_axis hη).symm
    _ = _ := by rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]

theorem graphAlgebraicDirection_eq (plus : Bool) {η : Plane} (hη : η ∈ graphPlaneSlit) (z : ℝ) :
    graphAlgebraicDirection plus (η,z) =
      sourceDirection (graphPlaneAngle η+(if plus then Real.arctan z else -Real.arctan z)) := by
  cases plus
  · simp only [graphAlgebraicDirection, Bool.false_eq_true, ↓reduceIte,
      graphNormalizedAxis_eq hη, neg_smul, ← sub_eq_add_neg]
    exact (sourceDirection_sub_arctan _ _).symm
  · simp only [graphAlgebraicDirection, ↓reduceIte, graphNormalizedAxis_eq hη]
    exact (sourceDirection_add_arctan _ _).symm

theorem graphAlgebraicDirection_uniform_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (plus : Bool) (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
      ‖iteratedFDeriv ℝ n (graphAlgebraicDirection plus) (η,z)‖ ≤ C := by
  let K : Set (Plane × ℝ) := closedBall 0 8 ∩ {p | 1/8 ≤ ‖p.1‖}
  have hK : IsCompact K := (isCompact_closedBall (0:Plane × ℝ) 8).inter_right
    (isClosed_le continuous_const continuous_fst.norm)
  have hc (plus : Bool) : ContinuousOn (iteratedFDeriv ℝ n (graphAlgebraicDirection plus)) K := by
    intro p hp
    have hr : 1/8 ≤ ‖p.1‖ := hp.2
    have hn : p.1 ≠ 0 := norm_pos_iff.mp (by linarith)
    exact ((graphAlgebraicDirection_contDiffAt plus p hn).continuousAt_iteratedFDeriv
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).continuousWithinAt
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (hc true)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (hc false)
  refine ⟨max 0 (max A B), le_max_left _ _, ?_⟩
  intro plus η z hη hz hlo
  have hp : (η,z) ∈ K := by
    refine ⟨?_,hlo⟩
    simp only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨hη,hz.trans (by norm_num)⟩
  cases plus
  · exact (hB _ hp).trans ((le_max_right A B).trans (le_max_right _ _))
  · exact (hA _ hp).trans ((le_max_left A B).trans (le_max_right _ _))

end PlanarFalconer

end OAI
