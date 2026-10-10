import OAI.Geometry.SurfaceImmersion.Atlas.CurvePhaseCriticalValues

namespace OAI

/-! Generic linear parts of the convex quadratic phases have only
nondegenerate critical points on each prescribed regular boundary arc. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
local instance genericCurveVolumeHaar : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

lemma curvePhaseVelocity_swap (u v : ℝ → CurvePlane) (L t : ℝ) (ell : CurvePlane) :
    curvePhaseVelocity (fun s => (u s).swap) (fun s => (v s).swap) L t ell.swap =
      curvePhaseVelocity u v L t ell := by
  dsimp [curvePhaseVelocity]
  ring

lemma curvePhaseAcceleration_swap (u v w : ℝ → CurvePlane) (L t : ℝ) (ell : CurvePlane) :
    curvePhaseAcceleration (fun s => (u s).swap) (fun s => (v s).swap)
      (fun s => (w s).swap) L t ell.swap = curvePhaseAcceleration u v w L t ell := by
  dsimp [curvePhaseAcceleration]
  ring

theorem curve_phase_all_degenerate_parameters_null
    (u v w : ℝ → CurvePlane) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hdu : ∀ t, HasDerivAt u (v t) t) (hdv : ∀ t, HasDerivAt v (w t) t) (L : ℝ) :
    volume {ell : CurvePlane | ∃ t, v t ≠ 0 ∧
      curvePhaseVelocity u v L t ell = 0 ∧ curvePhaseAcceleration u v w L t ell = 0} = 0 := by
  let B1 : Set CurvePlane := {ell | ∃ t, (v t).1 ≠ 0 ∧
    curvePhaseVelocity u v L t ell = 0 ∧ curvePhaseAcceleration u v w L t ell = 0}
  let B2 : Set CurvePlane := {ell | ∃ t, (v t).2 ≠ 0 ∧
    curvePhaseVelocity (fun s => (u s).swap) (fun s => (v s).swap) L t ell = 0 ∧
    curvePhaseAcceleration (fun s => (u s).swap) (fun s => (v s).swap)
      (fun s => (w s).swap) L t ell = 0}
  have h1 : volume B1 = 0 := curve_phase_degenerate_parameters_null u v w hu hv hdu hdv L
  have h2 : volume B2 = 0 := curve_phase_degenerate_parameters_null
    (fun s => (u s).swap) (fun s => (v s).swap) (fun s => (w s).swap)
    (hu.snd.prodMk hu.fst) (hv.snd.prodMk hv.fst)
    (fun t => (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hdu t))
    (fun t => (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hdv t)) L
  have hswap : Differentiable ℝ (Prod.swap : CurvePlane → CurvePlane) :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).differentiable
  have himage : volume (Prod.swap '' B2) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hswap.differentiableOn h2
  apply measure_mono_null _ (measure_union_null h1 himage)
  rintro ell ⟨t,hv0,hcrit,hdeg⟩
  by_cases hfirst : (v t).1 = 0
  · right
    have hsecond : (v t).2 ≠ 0 := by
      intro he
      apply hv0
      exact Prod.ext hfirst he
    refine ⟨ell.swap,⟨t,hsecond,?_,?_⟩,Prod.swap_swap ell⟩
    · simpa only [curvePhaseVelocity_swap] using hcrit
    · simpa only [curvePhaseAcceleration_swap] using hdeg
  · left
    exact ⟨t,hfirst,hcrit,hdeg⟩

/-- Countably many regular arcs can be handled in every prescribed open
set of phase parameters. -/
theorem exists_nondegenerate_curve_phases {α : Type*} [Countable α]
    (u v w : α → ℝ → CurvePlane) (hu : ∀ a, ContDiff ℝ ∞ (u a))
    (hv : ∀ a, ContDiff ℝ ∞ (v a))
    (hdu : ∀ a t, HasDerivAt (u a) (v a t) t)
    (hdv : ∀ a t, HasDerivAt (v a) (w a t) t) (L : α → ℝ)
    (U : Set CurvePlane) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ell ∈ U, ∀ a t, v a t ≠ 0 → curvePhaseVelocity (u a) (v a) (L a) t ell = 0 →
      curvePhaseAcceleration (u a) (v a) (w a) (L a) t ell ≠ 0 := by
  let B : α → Set CurvePlane := fun a => {ell | ∃ t, v a t ≠ 0 ∧
    curvePhaseVelocity (u a) (v a) (L a) t ell = 0 ∧
    curvePhaseAcceleration (u a) (v a) (w a) (L a) t ell = 0}
  have hb : volume (⋃ a, B a) = 0 := measure_iUnion_null (fun a =>
    curve_phase_all_degenerate_parameters_null (u a) (v a) (w a) (hu a) (hv a) (hdu a) (hdv a) (L a))
  have hdense : Dense (⋃ a, B a)ᶜ := Measure.dense_of_ae (μ := (volume : Measure CurvePlane))
    (by simpa only [ae_iff,mem_compl_iff,not_not,Set.ofPred_mem_eq] using hb)
  obtain ⟨ell,hell,hellB⟩ := hdense.inter_open_nonempty U hU hne
  refine ⟨ell,hell,?_⟩
  intro a t ht hc hz
  exact hellB (mem_iUnion.mpr ⟨a,t,ht,hc,hz⟩)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
