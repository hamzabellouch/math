import OAI.MeasureTheory.Falconer.Graphs.GraphAlgebraicDirections
import OAI.MeasureTheory.Falconer.Estimates.FrechetCompositionScale
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace OAI

namespace PlanarFalconer
open Set Metric Filter
open scoped ContDiff Topology

noncomputable def graphComplexCoordinate (η : Plane) : ℂ :=
  Complex.orthonormalBasisOneI.repr.symm η

theorem graphComplexCoordinate_contDiff : ContDiff ℝ ∞ graphComplexCoordinate :=
  Complex.orthonormalBasisOneI.repr.symm.contDiff

theorem graphComplexCoordinate_norm (η : Plane) : ‖graphComplexCoordinate η‖ = ‖η‖ :=
  Complex.orthonormalBasisOneI.repr.symm.norm_map η

theorem graphPlaneAngle_eq_arg (η : Plane) :
    graphPlaneAngle η = Complex.arg (graphComplexCoordinate η) := by
  change Complex.arg (Complex.equivRealProd.symm (graphPlaneEquiv.symm η)) = _
  congr 1
  apply Complex.orthonormalBasisOneI.repr.injective
  ext i
  fin_cases i <;> simp [graphPlaneEquiv, graphComplexCoordinate,
    Complex.orthonormalBasisOneI_repr_apply]

theorem periodic_eq_of_angle_eq {f : ℝ → ℂ} (hp : Function.Periodic f (2*Real.pi))
    {a b : ℝ} (he : (a : Real.Angle) = (b : Real.Angle)) : f a = f b := by
  exact congrArg hp.lift he

theorem periodic_arg_neg {f : ℝ → ℂ} (hp : Function.Periodic f (2*Real.pi))
    {w : ℂ} (hw : w ≠ 0) (c : ℝ) :
    f (Complex.arg (-w)+Real.pi+c) = f (Complex.arg w+c) := by
  apply periodic_eq_of_angle_eq hp
  simp only [Real.Angle.coe_add, Complex.arg_neg_coe_angle hw]
  congr 1
  rw [add_assoc, ← Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, add_zero]

theorem complex_arg_contDiffAt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg w := by
  have hl : ContDiffAt ℝ ∞ Complex.log w :=
    (show ContDiffAt ℂ ∞ Complex.log w from Complex.contDiffAt_log hw).restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using Complex.imCLM.contDiff.contDiffAt.comp w hl

noncomputable def graphAngleCoordinate (positive plus : Bool) (p : Plane × ℝ) : ℝ :=
  Complex.arg (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1) +
    (if plus then Real.arctan p.2 else -Real.arctan p.2)

noncomputable def graphAngularPullback (f : ℝ → ℂ) (plus : Bool) (c : ℝ)
    (p : Plane × ℝ) : ℂ := f (graphPlaneAngle p.1 +
      (if plus then Real.arctan p.2 else -Real.arctan p.2)+c)

theorem graphAngularPullback_chart {f : ℝ → ℂ} (hp : Function.Periodic f (2*Real.pi))
    (positive plus : Bool) (c : ℝ) {p : Plane × ℝ} (hη : p.1 ≠ 0) :
    graphAngularPullback f plus c p =
      f (graphAngleCoordinate positive plus p + (if positive then 0 else Real.pi)+c) := by
  have hw : graphComplexCoordinate p.1 ≠ 0 := by
    intro he
    have := graphComplexCoordinate_norm p.1
    rw [he, norm_zero] at this
    exact hη (norm_eq_zero.mp this.symm)
  cases positive
  · simp only [graphAngularPullback, graphAngleCoordinate, Bool.false_eq_true, ↓reduceIte,
      graphPlaneAngle_eq_arg]
    convert (periodic_arg_neg hp hw ((if plus then Real.arctan p.2 else -Real.arctan p.2)+c)).symm using 1 <;>
      congr 1 <;> ring
  · simp [graphAngularPullback, graphAngleCoordinate, graphPlaneAngle_eq_arg]

theorem graphAngleCoordinate_contDiffAt (positive plus : Bool) {p : Plane × ℝ}
    (hp : (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1)
      ∈ Complex.slitPlane) : ContDiffAt ℝ ∞ (graphAngleCoordinate positive plus) p := by
  have hw : ContDiff ℝ ∞ (fun q : Plane × ℝ =>
      if positive then graphComplexCoordinate q.1 else -graphComplexCoordinate q.1) := by
    cases positive
    · exact (graphComplexCoordinate_contDiff.comp contDiff_fst).neg
    · exact graphComplexCoordinate_contDiff.comp contDiff_fst
  have hz : ContDiff ℝ ∞ (fun q : Plane × ℝ =>
      if plus then Real.arctan q.2 else -Real.arctan q.2) := by
    cases plus
    · exact (Real.contDiff_arctan.comp contDiff_snd).neg
    · exact Real.contDiff_arctan.comp contDiff_snd
  exact ((complex_arg_contDiffAt hp).comp p hw.contDiffAt).add hz.contDiffAt

def graphAngleCompact (positive : Bool) : Set (Plane × ℝ) :=
  (closedBall 0 8 ∩ {p | 1/8 ≤ ‖p.1‖}) ∩
    {p | 0 ≤ (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1).re}

theorem graphAngleCompact_isCompact (positive : Bool) : IsCompact (graphAngleCompact positive) := by
  have hc : Continuous (fun p : Plane × ℝ =>
      (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1).re) := by
    cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop [graphComplexCoordinate]
  exact ((isCompact_closedBall (0:Plane × ℝ) 8).inter_right
    (isClosed_le continuous_const continuous_fst.norm)).inter_right
      (isClosed_le continuous_const hc)

theorem graphAngleCompact_slit (positive : Bool) {p : Plane × ℝ}
    (hp : p ∈ graphAngleCompact positive) :
    (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1)
      ∈ Complex.slitPlane := by
  let w := if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1
  have hn : ‖w‖ = ‖p.1‖ := by
    cases positive <;> simp [w, graphComplexCoordinate_norm]
  have hlo : (1:ℝ)/8 ≤ ‖p.1‖ := hp.1.2
  have hw : w ≠ 0 := norm_pos_iff.mp (by rw [hn]; linarith)
  have hr : 0 ≤ w.re := hp.2
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hi : w.im = 0
  · left
    apply lt_of_le_of_ne hr
    intro he
    apply hw
    apply Complex.ext <;> simp [he.symm, hi]
  · exact Or.inr hi

theorem graphAngleCompact_cover {η : Plane} {z : ℝ}
    (hhi : ‖η‖ ≤ 8) (hz : |z| ≤ 4) (hlo : 1/8 ≤ ‖η‖) :
    ∃ positive : Bool, (η,z) ∈ graphAngleCompact positive := by
  have hmem : (η,z) ∈ closedBall (0:Plane × ℝ) 8 ∩ {p | 1/8 ≤ ‖p.1‖} := by
    refine ⟨?_,hlo⟩
    simp only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨hhi,hz.trans (by norm_num)⟩
  by_cases hr : 0 ≤ (graphComplexCoordinate η).re
  · exact ⟨true,hmem,hr⟩
  · exact ⟨false,hmem,by simpa using (neg_nonneg.mpr (le_of_not_ge hr))⟩

end PlanarFalconer

end OAI
