import OAI.Geometry.NodalSets.Coefficients.SeedCoefficientPlacement

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma seedCoordImag_fderiv_ne {x : Coord}
    (hx : seedChartAmbient (seedCoordEquiv x) ∈ seedLogDomain)
    (hn : fderiv ℝ seedImagChart (seedCoordEquiv x) ≠ 0) :
    fderiv ℝ seedCoordImag x ≠ 0 := by
  rw [seedCoordImag,fderiv_comp x
    ((seedImagChart_smoothAt hx).differentiableAt (by simp))
    seedCoordEquiv.differentiableAt,seedCoordEquiv.fderiv]
  intro h
  apply hn
  ext v
  have he := congrArg (fun L : Coord →L[ℝ] ℝ ↦ L (seedCoordEquiv.symm v)) h
  simpa using he

theorem seed_coefficient_noncritical_placement : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    seedCoordCube a ⊆ seedCoordPatch r ∧
    closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
    (∀ x ∈ closure (seedCoordPatch r), fderiv ℝ seedCoordImag x ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel, ContDiff ℝ ∞ c →
      (∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α)) →
      (∀ y (α β : BaseModel →L[ℝ] ℝ), α ((c y).1 β) = β ((c y).1 α)) →
      (∀ y, 0 < (c y).2) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ K : Set Coord, IsCompact K → K ⊆ seedCoordPatch r →
      ∀ T : ℝ, SeedEnvelopePlaced (seedCoordMetric c) r a K T := by
  obtain ⟨r,a,δ,hr,ha,hδ,hK,hsub,hbranch,hseed⟩ := seed_envelope_Coord_patch
  have hDP := seedCoordCube_subset hsub
  have hPB : closure (seedCoordPatch r) ⊆ seedCoordBranch := fun x hx ↦
    (hbranch _ (seedCoordPatch_closure_subset r hx)).1
  refine ⟨r,a,δ,hr,ha,hδ,hDP,hPB,?_,?_⟩
  · intro x hx
    exact seedCoordImag_fderiv_ne (hbranch _ (seedCoordPatch_closure_subset r hx)).1
      (hbranch _ (seedCoordPatch_closure_subset r hx)).2
  intro c hc hp hs hρ hclose K hK hKP T
  have hsa : sourceDirectionalAdmissibleOn (seedCoordMetric c) seedCoordReal
      (closure (seedCoordPatch r)) := by
    intro x hx
    obtain ⟨hpos,hn,v,hpv,hv,hstr⟩ := hseed c
      (fun y _ ↦ hc.differentiable (by simp) y) (fun y _ ↦ hp y)
      (fun y _ ↦ hρ y) hclose x (seedCoordPatch_closure_subset r hx)
    exact ⟨hn,v,hv,hpv,hstr⟩
  have he := exists_placed_envelope (fun _ ↦ -a) (by positivity : 0 < 2*a)
    (seedCoordMetric c) seedCoordReal (seedCoordPatch_open r) (seedCoordPatch_compactClosure r)
    seedCoordBranch_open hPB (by simpa only [seedCoordCube_Icc] using hDP) hK hKP
    (seedCoordMetric_smooth c hc hp).contDiffOn seedCoordReal_smoothOn
    (fun x _ ↦ seedCoordMetric_positive c hp hρ x)
    (fun x _ ↦ seedCoordMetric_symmetric c hp hs x) hsa T
  simpa only [SeedEnvelopePlaced,seedCoordCube_Icc] using he

end
end Yau.Target

end OAI
