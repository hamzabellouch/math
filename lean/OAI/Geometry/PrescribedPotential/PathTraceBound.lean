import Mathlib
import OAI.Geometry.PrescribedPotential.ChernLuMaximum
import OAI.Geometry.PrescribedPotential.MetricInverseTrace
import OAI.Geometry.PrescribedPotential.PathFrameBounds
import OAI.Geometry.PrescribedPotential.PathPotentialBound
import OAI.Geometry.PrescribedPotential.PathRicci

namespace OAI

/-! Path Trace Bound. -/

section

 

noncomputable section
open Set Metric Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
open KaehlerCalculus
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty (Fin d)] {A : ComplexAtlas d X}

theorem volumePath_inverseTrace_bound_pos_dim (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (t b : ℝ) (φ : SmoothRealFunction A),
      t ∈ Icc 0 1 → ∀ hs : SolvesVolumePath g h t φ b,
      ∀ x, ((g.deform φ hs.choose).inverseTrace g).value x ≤ R := by
  classical
  obtain ⟨S,hS⟩ := CoordinateBall.finite_cover (A := A)
  choose C hC hCb using (fun p : S => p.val.path_frame_bound g h)
  let K : ℝ := ∑ p : S, C p
  have hK : 0 ≤ K := Finset.sum_nonneg (fun p _ => hC p)
  have hCK (p : S) : C p ≤ K := Finset.single_le_sum (fun q _ => hC q) (Finset.mem_univ p)
  obtain ⟨L,hL,hLb⟩ := volumePath_oscillation_bound g h
  refine ⟨(K+1)*d*Real.exp ((K+1)*L),by positivity,?_⟩
  intro t b φ ht hs x
  let M := g.deform φ hs.choose
  let f := M.inverseTrace g
  let Q : X → ℝ := fun y => Real.log (f.value y)-(K+1)*φ.value y
  have hfp : ∀ y, 0 < f.value y := fun y => M.inverseTrace_positive g y
  have hQc : Continuous Q := (f.continuous.log (fun y => ne_of_gt (hfp y))).sub
    (continuous_const.mul φ.continuous)
  obtain ⟨xm,_,hm⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hQc.continuousOn
  obtain ⟨p,hp,hxm⟩ := hS xm
  have hxmi : xm ∈ (A.chart p.index).source := by
    simpa only [ComplexAtlas.euclideanChart_source] using hxm.1
  let z := A.chart p.index xm
  have hz : z ∈ (A.chart p.index).target := (A.chart p.index).mapsTo hxmi
  have hb : ∀ B : Matrix (Fin d) (Fin d) ℂ,
      -K*(frameGram (g.matrix p.index z) B)^2 ≤ frameResidual
        (PotentialKaehler.potentialMatrix (fun y => Real.log (M.matrix p.index y).det.re) z)
        (g.matrix p.index z) (curvatureDiagonal (g.matrix p.index) z) B := by
    intro B
    rw [volumePath_logdet_hessian g h hs hs.choose p.index hz]
    have hh := hCb ⟨p,hp⟩ t ht xm hxm B
    exact (mul_le_mul_of_nonneg_right (neg_le_neg (hCK ⟨p,hp⟩)) (sq_nonneg _)).trans hh
  have hmax : IsLocalMax (fun y => Real.log (inverseTrace (M.matrix p.index) (g.matrix p.index) y)-
      (K+1)*φ.localExpression p.index y) z := by
    change ∀ᶠ y in 𝓝 z, _ ≤ _
    filter_upwards [(A.chart p.index).open_target.mem_nhds hz] with y hy
    have hyS := M.inverseTrace_local g p.index hy
    have hzS := M.inverseTrace_local g p.index hz
    rw [← hyS,← hzS]
    change Q ((A.chart p.index).symm y) ≤ Q ((A.chart p.index).symm z)
    rw [show (A.chart p.index).symm z = xm from (A.chart p.index).left_inv hxmi]
    exact hm (mem_univ _)
  have hMmax : f.value xm ≤ (K+1)*d := by
    change M.inverseTraceValue g xm ≤ _
    rw [M.inverseTraceValue_local g p.index hxmi]
    exact inverseTrace_at_localMax_bound (A.chart p.index).open_target (M.smooth p.index)
      (M.positive p.index) (M.closed p.index) (g.smooth p.index) (g.positive p.index)
      (φ.smooth p.index) hz rfl K hb hmax
  have hqm : Real.log (f.value x)-(K+1)*φ.value x ≤
      Real.log (f.value xm)-(K+1)*φ.value xm := hm (mem_univ x)
  have hφ := (abs_le.mp (hLb t b φ ht hs x xm)).2
  have ha : 0 ≤ K+1 := by linarith
  have hl : Real.log (f.value x) ≤ Real.log (f.value xm)+(K+1)*L := by
    have hh := mul_le_mul_of_nonneg_left hφ ha
    nlinarith only [hqm,hh]
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_add,Real.exp_log (hfp x),Real.exp_log (hfp xm)] at he
  exact he.trans (mul_le_mul_of_nonneg_right hMmax (Real.exp_pos _).le)
omit [Nonempty (Fin d)] in
 
theorem volumePath_inverseTrace_bound (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (t b : ℝ) (φ : SmoothRealFunction A),
      t ∈ Icc 0 1 → ∀ hs : SolvesVolumePath g h t φ b,
      ∀ x, ((g.deform φ hs.choose).inverseTrace g).value x ≤ R := by
  by_cases hd : d = 0
  · subst d
    refine ⟨0,le_rfl,?_⟩
    intro t b φ ht hs x
    simp [KaehlerMetric.inverseTrace,KaehlerMetric.inverseTraceValue,KaehlerCalculus.inverseTrace,
      Matrix.trace]
  · let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
    exact volumePath_inverseTrace_bound_pos_dim g h
end Anticanonical.SourceSmooth

end
end

end OAI
