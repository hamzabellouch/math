import OAI.Geometry.SurfaceImmersion.Geometry.FiniteCurveTangencies

namespace OAI

/-! On compact regular arcs the nondegenerate phase parameters form an
open dense set, suitable for independent choices in a finite product. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
local instance compactCurveVolumeHaar : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

def goodCompactCurvePhases (u v w : ℝ → CurvePlane) (L : ℝ) (K : Set ℝ) : Set CurvePlane :=
  {ell | ∀ t ∈ K, curvePhaseVelocity u v L t ell = 0 →
    curvePhaseAcceleration u v w L t ell ≠ 0}

theorem goodCompactCurvePhases_open (u v w : ℝ → CurvePlane) (L : ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    {K : Set ℝ} (hK : IsCompact K) : IsOpen (goodCompactCurvePhases u v w L K) := by
  rw [isOpen_iff_mem_nhds]
  intro ell hell
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  let F : CurvePlane × ℝ → CurvePlane := fun z =>
    (curvePhaseVelocity u v L z.2 z.1,curvePhaseAcceleration u v w L z.2 z.1)
  have hF : Continuous F := by
    dsimp [F,curvePhaseVelocity,curvePhaseAcceleration]
    fun_prop
  have hne : F (ell,t) ≠ 0 := by
    intro he
    have hv0 : curvePhaseVelocity u v L t ell = 0 := congrArg Prod.fst he
    have ha0 : curvePhaseAcceleration u v w L t ell = 0 := congrArg Prod.snd he
    exact hell t ht hv0 ha0
  filter_upwards [hF.continuousAt.eventually_ne hne] with z hz
  intro hv0 ha0
  apply hz
  exact Prod.ext hv0 ha0

theorem goodCompactCurvePhases_dense
    (u v w : ℝ → CurvePlane) (L : ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hdu : ∀ t, HasDerivAt u (v t) t) (hdv : ∀ t, HasDerivAt v (w t) t)
    (K : Set ℝ) (hregular : ∀ t ∈ K, v t ≠ 0) :
    Dense (goodCompactCurvePhases u v w L K) := by
  have hnull : volume (goodCompactCurvePhases u v w L K)ᶜ = 0 := by
    apply measure_mono_null _ (curve_phase_all_degenerate_parameters_null u v w hu hv hdu hdv L)
    intro ell hell
    change ¬ (∀ t ∈ K, curvePhaseVelocity u v L t ell = 0 →
      curvePhaseAcceleration u v w L t ell ≠ 0) at hell
    push Not at hell
    obtain ⟨t,ht,hcrit,hdeg⟩ := hell
    exact ⟨t,hregular t ht,hcrit,hdeg⟩
  apply Measure.dense_of_ae (μ := (volume : Measure CurvePlane))
  rw [ae_iff]
  exact hnull

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
