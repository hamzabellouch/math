import OAI.Analysis.HotSpots.TraceRank

namespace OAI

section ActualNoncritical

noncomputable section
open Set MeasureTheory Filter Metric Function Module
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10 HilbertMultipliers
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)




theorem noncritical_at_disk (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
    (p : disk) : gradient u (c.F p) ≠ 0 := by
  intro hz
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hμ := firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne
  obtain ⟨d,hd,hd1,hsub⟩ := c.subcritical hΩ.2.2.1 hΩ.1 hμ
  obtain ⟨H,hN,hI,hC,hS,b,B,hinj,hb,hid⟩ := full_boundary_hilbert_embedding
    c.densityBound_ne_top (c.density_bound hμ.le) hd.le hd1 hsub p
  let := hN
  let := hI
  let := hC
  let := hS
  obtain ⟨I,e,_he⟩ := exists_hilbertBasis ℝ H
  let : Countable I := orthonormal_countable e.orthonormal
  have hnull := c.coordinate_null_trace hΩ hu hne p hz e hb hid
  have hY : ContinuousOn (closedGradient Ω u) (closure Ω) :=
    closedGradient_continuous hΩ.2.1 hΩ.2.2.2.2 hu.1
  have he : EqOn (gradient u) (closedGradient Ω u) Ω := fun _ hx => (closedGradient_eq hΩ.2.1 hx).symm
  let J : closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 :=
    ⟨closedEigenJet Ω u (closedGradient Ω u),u,closedGradient Ω u,hu.interior,hu.1.continuousOn,hY,he,rfl⟩
  let T := closedTraceSpace c hΩ
  let g : T := ⟨closedGradientTrace c hΩ J,J,rfl⟩
  have hgv (s : Circle) : g.val s = closedGradient Ω u (c.F (circleBoundary s)) := rfl
  obtain ⟨hf,hr⟩ := closedTraceSpace_rank c hΩ
  let : Module.Finite ℝ T := hf
  have hmem (i : I) : (fun s => inner ℝ (e i) (b (circleBoundary s)) • g.val s) ∈ T := by
    obtain ⟨v,Y,hv,hvc,hY,hvY,ht⟩ := hnull i
    let K : closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 :=
      ⟨closedEigenJet Ω v Y,v,Y,hv,hvc,hY,hvY,rfl⟩
    refine ⟨K,?_⟩
    funext s
    exact ht (circleBoundary s)
  have h0 := multiplier_contradiction e (hb.continuous.comp circleBoundary.continuous)
    (hinj.comp circleBoundary.injective) T hr (fun U hU hne => closedTraceSpace_local_rank c hΩ hU hne)
    g ((c.closedGradient_trace_continuous hΩ hu).comp circleBoundary.continuous) hmem
  apply c.boundary_gradient_not_zero hΩ hu.interior hu.1.continuousOn hY he hne
  intro x hx
  have hh := congrArg (fun f : T => f.val (c.circleBoundaryHomeomorph.symm ⟨x,hx⟩)) h0
  change closedGradient Ω u
    (c.circleBoundaryHomeomorph (c.circleBoundaryHomeomorph.symm ⟨x,hx⟩)) = 0 at hh
  simpa only [Homeomorph.apply_symm_apply] using hh

include c


theorem noncritical (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0) :
    ∀ x ∈ Ω, gradient u x ≠ 0 := by
  intro x hx
  have hp : c.G x ∈ disk := by
    have hh := c.diskMap.map_target hx
    change c.diskMap.symm x ∈ disk at hh
    rwa [c.diskMap_inverse_agrees hx] at hh
  have hh := c.noncritical_at_disk hΩ hu hne ⟨c.G x,hp⟩
  simpa only [c.right_inverse x (subset_closure hx)] using hh
end StrictHotSpots.Conformal.ClosedDiskChart

namespace StrictHotSpots


theorem main_theorem (Ω : Set Plane) (hΩ : AdmissibleDomain Ω)
    (u : Plane → ℝ) (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : MainConclusion Ω u := by
  obtain ⟨c⟩ := Conformal.exists_closed_disk_chart hΩ
  exact strict_boundary_extrema_of_noncritical hΩ.1 hΩ.2.1 hΩ.2.2.1 hu.1.continuousOn
    (c.noncritical hΩ hu hne)
end StrictHotSpots
end
end ActualNoncritical


end OAI
