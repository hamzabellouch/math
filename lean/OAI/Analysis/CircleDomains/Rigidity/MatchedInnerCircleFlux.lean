import OAI.Analysis.CircleDomains.Rigidity.MatchedDiskNeighborhood
import OAI.Analysis.CircleDomains.Rigidity.QuadrantFlux

namespace OAI

/-! The inner-circle flux bound uses the actual closed correspondence,
not a boundary extension of the conformal map. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem quadrantPoint_dist (c : ℂ) (r : ℝ) (s t : Bool) (θ : ℝ) :
    dist (quadrantPoint c r s t θ) c = |r| := by
  simp only [quadrantPoint,dist_eq_norm,add_sub_cancel_left,norm_mul,
    quadrantNormal_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem indexed_quadrantFlux_bound (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (j : D.IndexedMatchedPair)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioc (0 : ℝ) δ,
      |quadrantFlux (D.selectedPlane hG hf) (E.sourceCenter j) (E.sourceRadius j+ρ)| ≤
        2*Real.pi*(E.sourceRadius j+ρ)*(E.targetRadius j+ε) := by
  obtain ⟨δ,hδ,hnear⟩ := D.selectedPlane_near_indexed_disk E hG hf j hε
  refine ⟨δ,hδ,?_⟩
  intro ρ hρ
  have hr : 0 ≤ E.sourceRadius j+ρ := add_nonneg (E.source_nonneg j) hρ.1.le
  apply quadrantFlux_near_const (b := E.targetCenter j) hr
    (add_nonneg (E.target_nonneg j) hε.le)
  intro s t θ _
  apply (hnear _ ?_).le
  rw [mem_closedBall,quadrantPoint_dist,abs_of_nonneg hr]
  exact add_le_add le_rfl hρ.2

 theorem indexed_quadrantFlux_limiting_bound (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (j : D.IndexedMatchedPair)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioc (0 : ℝ) δ,
      quadrantFlux (D.selectedPlane hG hf) (E.sourceCenter j) (E.sourceRadius j+ρ) ≤
        2*Real.pi*E.sourceRadius j*E.targetRadius j+ε := by
  have hc : ContinuousAt (fun t : ℝ => 2*Real.pi*(E.sourceRadius j+t)*(E.targetRadius j+t)) 0 := by fun_prop
  obtain ⟨ζ,hζ,hζbound⟩ := Metric.continuousAt_iff.mp hc ε hε
  let η := min (ζ/2) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hηζ : η < ζ := (min_le_left (ζ/2) 1).trans_lt (by linarith)
  have hlimit := hζbound (show dist η 0 < ζ by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hη] using hηζ)
  obtain ⟨δ,hδ,hbound⟩ := D.indexed_quadrantFlux_bound E hG hf j hη
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro ρ hρ
  have hb := hbound ρ ⟨hρ.1,hρ.2.trans (min_le_left _ _)⟩
  have hρη : ρ ≤ η := hρ.2.trans (min_le_right _ _)
  have hm : 2*Real.pi*(E.sourceRadius j+ρ)*(E.targetRadius j+η) ≤
      2*Real.pi*(E.sourceRadius j+η)*(E.targetRadius j+η) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hρη)
      (mul_nonneg (by norm_num) Real.pi_pos.le)) (add_nonneg (E.target_nonneg j) hη.le)
  have hlim : 2*Real.pi*(E.sourceRadius j+η)*(E.targetRadius j+η) <
      2*Real.pi*E.sourceRadius j*E.targetRadius j+ε := by
    rw [dist_eq_norm,Real.norm_eq_abs] at hlimit
    simp only [add_zero] at hlimit
    linarith [(abs_lt.mp hlimit).2]
  exact (le_abs_self _).trans (hb.trans (hm.trans hlim.le))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
