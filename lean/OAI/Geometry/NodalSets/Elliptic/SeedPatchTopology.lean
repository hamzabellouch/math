import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateCube

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff Topology
noncomputable section
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

def seedSpherePatch (r : ℝ) : Set Base :=
  (extChartAt (𝓡 4) seedPoint).symm '' ball (0 : BaseModel) r

def seedSphereCube (a : ℝ) : Set Base :=
  (extChartAt (𝓡 4) seedPoint).symm '' seedCoordinateCube a

lemma seedSpherePatch_open (r : ℝ) : IsOpen (seedSpherePatch r) := by
  change IsOpen ((stereographic' 4 (-seedPoint)).symm '' ball (0 : BaseModel) r)
  exact (stereographic' 4 (-seedPoint)).isOpen_image_symm_of_subset_target isOpen_ball (by simp)

lemma seedSpherePatch_center {r : ℝ} (hr : 0 < r) : seedPoint ∈ seedSpherePatch r := by
  exact ⟨0,mem_ball_self hr,centeredSphereChart_inverse_zero seedPoint⟩

lemma seedSphereChart_inverse_continuous : Continuous (extChartAt (𝓡 4) seedPoint).symm := by
  apply continuousOn_univ.mp
  simpa only [centeredSphereChart_target] using continuousOn_extChartAt_symm (I := 𝓡 4) seedPoint

lemma seedSpherePatch_closure_subset (r : ℝ) :
    closure (seedSpherePatch r) ⊆
      (extChartAt (𝓡 4) seedPoint).symm '' closedBall (0 : BaseModel) r := by
  apply closure_minimal (image_mono ball_subset_closedBall)
  exact ((isCompact_closedBall _ _).image seedSphereChart_inverse_continuous).isClosed

lemma seedSpherePatch_compactClosure (r : ℝ) : IsCompact (closure (seedSpherePatch r)) :=
  ((isCompact_closedBall _ _).image seedSphereChart_inverse_continuous).of_isClosed_subset
    isClosed_closure (seedSpherePatch_closure_subset r)

lemma seedSpherePatch_closure_in_chart (r : ℝ) :
    closure (seedSpherePatch r) ⊆ (extChartAt (𝓡 4) seedPoint).source := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := seedSpherePatch_closure_subset r hx
  exact (extChartAt (𝓡 4) seedPoint).map_target (by rw [centeredSphereChart_target]; trivial)

lemma seedSphereCube_compact {a : ℝ} (ha : 0 ≤ a) : IsCompact (seedSphereCube a) :=
  (seedCoordinateCube_compact ha).image seedSphereChart_inverse_continuous

lemma seedSphereCube_subset {a r : ℝ} (h : seedCoordinateCube a ⊆ ball (0 : BaseModel) r) :
    seedSphereCube a ⊆ seedSpherePatch r := image_mono h

lemma seedImagChart_nonzero_implies_manifold {y : BaseModel}
    (hy : seedChartAmbient y ∈ seedLogDomain) (hd : fderiv ℝ seedImagChart y ≠ 0) :
    mfderiv (𝓡 4) 𝓘(ℝ,ℝ) sphereSeedLogImag ((extChartAt (𝓡 4) seedPoint).symm y) ≠ 0 := by
  have hs := (sphereSeedLogImag_smoothAt hy).mdifferentiableAt (by simp)
  have hc := (inverse_chart_smooth_at (I := 𝓡 4) seedPoint
    (y := y) (by rw [centeredSphereChart_target]; trivial)).mdifferentiableAt (by simp)
  have he := mfderiv_comp y hs hc
  rw [mfderiv_eq_fderiv] at he
  intro hz
  apply hd
  change fderiv ℝ (sphereSeedLogImag ∘ (extChartAt (𝓡 4) seedPoint).symm) y = 0
  rw [he,hz,ContinuousLinearMap.zero_comp]
  rfl

lemma seedSpherePatch_log_closure {r : ℝ}
    (h : ∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) :
    ∀ x ∈ closure (seedSpherePatch r), (x : SeedAmbient) ∈ seedLogDomain ∧
      mfderiv (𝓡 4) 𝓘(ℝ,ℝ) sphereSeedLogImag x ≠ 0 := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := seedSpherePatch_closure_subset r hx
  exact ⟨(h y hy).1,seedImagChart_nonzero_implies_manifold (h y hy).1 (h y hy).2⟩

end
end Yau.Target

end OAI
