import OAI.Analysis.CircleDomains.Rigidity.PrincipalOuterFlux
import OAI.Analysis.CircleDomains.Rigidity.MatchedDiskDomainGeometry
import OAI.Analysis.CircleDomains.Topology.LimitSphereExtension

namespace OAI

/-! Transfer the principal outer flux to the actual selected field on
large circles wholly contained in the source domain. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem selected_principal_quadrantFlux (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hnorm : IsPrincipalNormalized f) :
    ∃ R₀ > 0, ∀ R ≥ R₀, quadrantFlux (D.selectedPlane hG hf) 0 R = 2*Real.pi*R^2 := by
  obtain ⟨A,hA,hbound⟩ := finite_domain_exterior_radius hG hinf
  have hmem : ∀ᶠ (z : ℂ) in cobounded ℂ, (z : Sphere) ∈ G := by
    have hm := OnePoint.tendsto_coe_infty (hG.mem_nhds hinf)
    change {z : ℂ | (z : Sphere) ∈ G} ∈ cobounded ℂ
    rw [Metric.cobounded_eq_cocompact]
    rw [coclosedCompact_eq_cocompact] at hm
    exact hm
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ (fun z : ℂ => finiteCoord (f (z : Sphere))) z := by
    filter_upwards [hmem] with z hz
    exact (analyticAt_finite_map_of_conformal hG hf.1 hz
      (D.planeRelation_ne_infty hG hinf hf hnorm.1 (D.componentRelation_graph hf hz))).differentiableAt
  obtain ⟨B,hB,hflux⟩ := eventually_principal_quadrantFlux hd (principal_remainder_tendsto_zero hnorm.2)
  refine ⟨max B (A+1),lt_of_lt_of_le hB (le_max_left _ _),?_⟩
  intro R hR
  have hRA : A < R := by have := (le_max_right B (A+1)).trans hR; linarith
  have hRp : 0 < R := hA.trans hRA
  have hepoint (s t : Bool) (θ : ℝ) :
      D.selectedPlane hG hf (quadrantPoint 0 R s t θ) =
        finiteCoord (f (quadrantPoint 0 R s t θ : Sphere)) := by
    apply D.selectedPlane_eq_finite_part hG hf
    by_contra hz
    have hn := quadrantPoint_dist 0 R s t θ
    rw [dist_zero_right,abs_of_pos hRp] at hn
    have hb := hbound _ hz
    rw [hn] at hb
    exact (not_lt_of_ge hRA.le) hb
  have he : quadrantFlux (D.selectedPlane hG hf) 0 R =
      quadrantFlux (fun z : ℂ => finiteCoord (f (z : Sphere))) 0 R := by
    unfold quadrantFlux
    simp_rw [hepoint]
  exact he.trans (hflux R ((le_max_left _ _).trans hR))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
