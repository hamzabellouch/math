import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalBump

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def graphPlaneSlit : Set Plane := graphPlaneEquiv.symm ⁻¹' polarCoord.source

def graphGlobalAnnulus (a b z : ℝ) : Set Plane :=
  {η | ‖η‖*Real.sqrt (1+z^2)/2 ∈ Ioo a b}

theorem graphGlobalSlice_eq {a b : ℝ} (ha : 0 < a) (z : ℝ) :
    graphGlobalSlice a b z = graphPlaneSlit ∩ graphGlobalAnnulus a b z := by
  ext η
  have hs : 0 < Real.sqrt (1+z^2) := by positivity
  constructor
  · rintro ⟨x,⟨p,hp,rfl⟩,rfl⟩
    have hdom := graphPolarRectangle_subset
      (by positivity : 0 < 2*a/Real.sqrt (1+z^2)) hp
    constructor
    · change graphPlaneEquiv.symm (graphPlaneEquiv (polarCoord.symm p)) ∈ polarCoord.source
      rw [MeasurableEquiv.symm_apply_apply]
      exact polarCoord.map_target hdom
    · change ‖graphPlaneEquiv (polarCoord.symm p)‖*Real.sqrt (1+z^2)/2 ∈ Ioo a b
      rw [graphPlaneEquiv_norm, polarCoord.right_inv hdom]
      have hlo := (div_lt_iff₀ hs).mp hp.1.1
      have hhi := (lt_div_iff₀ hs).mp hp.1.2
      constructor <;> linarith
  · rintro ⟨hslit,hrad⟩
    change graphPlaneEquiv.symm η ∈ polarCoord.source at hslit
    change a < ‖η‖*Real.sqrt (1+z^2)/2 ∧ ‖η‖*Real.sqrt (1+z^2)/2 < b at hrad
    refine ⟨graphPlaneEquiv.symm η, ?_, MeasurableEquiv.apply_symm_apply _ _⟩
    refine ⟨polarCoord (graphPlaneEquiv.symm η), ?_, polarCoord.left_inv hslit⟩
    refine ⟨?_, (polarCoord.map_source hslit).2⟩
    rw [graphPlaneEquiv_symm_radius]
    exact ⟨(div_lt_iff₀ hs).mpr (by linarith [hrad.1]),
      (lt_div_iff₀ hs).mpr (by linarith [hrad.2])⟩

theorem graphPlaneSlit_ae_eq_univ : graphPlaneSlit =ᵐ[volume] univ := by
  have h := ((graphPlaneEquiv_volume_preserving.symm graphPlaneEquiv).quasiMeasurePreserving).preimage_ae_eq
    polarCoord_source_ae_eq_univ
  simpa only [graphPlaneSlit, preimage_univ] using h

theorem graphGlobalSlice_ae_eq_annulus {a b : ℝ} (ha : 0 < a) (z : ℝ) :
    graphGlobalSlice a b z =ᵐ[volume] graphGlobalAnnulus a b z := by
  rw [graphGlobalSlice_eq ha]
  filter_upwards [graphPlaneSlit_ae_eq_univ] with η hη
  change (η ∈ graphPlaneSlit) = True at hη
  have hm : η ∈ graphPlaneSlit := Eq.mp hη.symm trivial
  change (η ∈ graphPlaneSlit ∧ η ∈ graphGlobalAnnulus a b z) = (η ∈ graphGlobalAnnulus a b z)
  simp only [hm, true_and]

theorem graphGlobalAnnulus_measurable (a b z : ℝ) : MeasurableSet (graphGlobalAnnulus a b z) :=
  measurableSet_Ioo.preimage ((continuous_norm.mul continuous_const).div_const 2).measurable

theorem sourceArcLength_pair_graph_annulus_bump
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {R : ℝ} (hR : 0 < R) (axis : ℝ) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • F r u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalAnnulus (1/4) 4 z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          (Ψ (‖η‖*Real.sqrt (1+z^2)/2) •
            F (R*(‖η‖*Real.sqrt (1+z^2)/2))
              (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
              (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis))) := by
  rw [sourceArcLength_pair_graph_plane_bump hF hΨ hsupp hR axis]
  apply integral_congr_ae
  filter_upwards with z
  exact setIntegral_congr_set (graphGlobalSlice_ae_eq_annulus (by norm_num) z)

end PlanarFalconer

end OAI
