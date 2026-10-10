import OAI.Geometry.SurfaceImmersion.Atlas.GenericCurvePhases

namespace OAI

/-! Two independently perturbed phase covectors can avoid parallelism in
every open parameter set. Only the two-dimensional determinant is used. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ClosedSurfaceR4.PhaseGeometry
local instance nonparallelVolumeHaar : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

def covectorDet (v w : CurvePlane) : ℝ := v.1*w.2-v.2*w.1

def covectorDetMap (v : CurvePlane) : CurvePlane →L[ℝ] ℝ :=
  v.1 • ContinuousLinearMap.snd ℝ ℝ ℝ-v.2 • ContinuousLinearMap.fst ℝ ℝ ℝ

lemma covectorDetMap_apply (v w : CurvePlane) : covectorDetMap v w = covectorDet v w := rfl

lemma covectorDetMap_surjective {v : CurvePlane} (hv : v ≠ 0) :
    Function.Surjective (covectorDetMap v) := by
  intro r
  by_cases hfirst : v.1 = 0
  · have hsecond : v.2 ≠ 0 := by
      intro hs
      exact hv (Prod.ext hfirst hs)
    refine ⟨(-r/v.2,0),?_⟩
    change v.1*0-v.2*(-r/v.2) = r
    field_simp
    ring
  · refine ⟨(0,r/v.1),?_⟩
    change v.1*(r/v.1)-v.2*0 = r
    field_simp
    ring

lemma dense_nonzero_covectors : Dense ({0} : Set CurvePlane)ᶜ := by
  apply Measure.dense_of_ae (μ := (volume : Measure CurvePlane))
  simp only [ae_iff,mem_singleton_iff,not_not]
  exact measure_singleton 0

lemma covectorDet_open_dense :
    IsOpen {z : CurvePlane × CurvePlane | covectorDet z.1 z.2 ≠ 0} ∧
      Dense {z : CurvePlane × CurvePlane | covectorDet z.1 z.2 ≠ 0} := by
  have hc : Continuous (fun z : CurvePlane × CurvePlane => covectorDet z.1 z.2) := by
    dsimp [covectorDet]
    fun_prop
  refine ⟨isOpen_ne.preimage hc,?_⟩
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨⟨v,w⟩,hvw⟩ := hne
  obtain ⟨A,B,hA,hB,hvA,hwB,hAB⟩ := isOpen_prod_iff.mp hU v w hvw
  obtain ⟨v',hv'A,hv'⟩ := dense_nonzero_covectors.inter_open_nonempty A hA ⟨v,hvA⟩
  have hv0 : v' ≠ 0 := hv'
  have hR : Dense ({0} : Set ℝ)ᶜ := by
    apply Measure.dense_of_ae (μ := (volume : Measure ℝ))
    simp only [ae_iff,mem_singleton_iff,not_not]
    exact measure_singleton 0
  have hd := hR.preimage ((covectorDetMap v').isOpenMap (covectorDetMap_surjective hv0))
  obtain ⟨w',hw'B,hw'⟩ := hd.inter_open_nonempty B hB ⟨w,hwB⟩
  refine ⟨(v',w'),hAB ⟨hv'A,hw'B⟩,?_⟩
  exact hw'

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
