import OAI.Analysis.CircleDomains.Topology.DiskCrosscutJordan
import OAI.Analysis.CircleDomains.Topology.CrosscutSeparationInput

namespace OAI

/-! Exact open sides and relative frontiers for a disk crosscut ending at one. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma disk_crosscut_sides_at_one (hsch : PlanarSchoenflies)
    {a : ℂ} (p : Path a 1) (hi : Injective p)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = ball 0 1 \ range p ∧
      frontier U ∩ ball 0 1 = range p ∩ ball 0 1 ∧
      frontier V ∩ ball 0 1 = range p ∩ ball 0 1 := by
  obtain ⟨H,hf,_,hinside⟩ := exists_disk_crosscut_jordan hsch p hi hp ha ha1
  let E := (closure (jordanInterior H))ᶜ
  have hE : IsOpen E := isClosed_closure.isOpen_compl
  have hec : E ∩ sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha) :=
    disk_crosscut_exterior_circle p ha hp H hf hinside
  have hC : IsConnected (E ∩ sphere (0 : ℂ) 1) := by
    rw [hec]
    exact isConnected_boundaryClosingArc_complement ha ha1
  have hV : IsConnected (E ∩ ball (0 : ℂ) 1) := by
    refine ⟨?_, isPreconnected_inter_disk_of_circle hE
      (isConnected_exterior_jordanInterior H).isPreconnected hC.isPreconnected⟩
    obtain ⟨z,hzE,hzs⟩ := hC.nonempty
    apply closure_nonempty_iff.mp
    refine ⟨z, hE.inter_closure ?_⟩
    rw [closure_ball _ one_ne_zero]
    exact ⟨hzE,sphere_subset_closedBall hzs⟩
  have harc : Disjoint (range (boundaryClosingArc a ha)) (ball (0 : ℂ) 1) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t,rfl⟩ hz
    have hn := mem_ball_zero_iff.mp hz
    rw [boundaryClosingArc_norm] at hn
    exact lt_irrefl _ hn
  have hfront : frontier (jordanInterior H) ∩ ball (0 : ℂ) 1 = range p ∩ ball 0 1 := by
    rw [hf,union_inter_distrib_right,harc.inter_eq,union_empty]
  have hEf : frontier E = frontier (jordanInterior H) := by
    change frontier (closure (jordanInterior H))ᶜ = _
    rw [frontier_compl,frontier,closure_closure,interior_closure_jordanInterior,
      frontier,(jordanInterior_isOpen H).interior_eq]
  refine ⟨jordanInterior H,E ∩ ball 0 1,jordanInterior_isOpen H,hE.inter isOpen_ball,
    isConnected_jordanInterior H,hV,?_,?_,hfront,?_⟩
  · exact Set.disjoint_left.mpr (fun z hz hzE => hzE.1 (subset_closure hz))
  · ext z
    constructor
    · rintro (hz | ⟨hzE,hzb⟩)
      · refine ⟨hinside hz,?_⟩
        intro hzp
        have hzfront : z ∈ frontier (jordanInterior H) := hf ▸ Or.inl hzp
        rw [frontier,(jordanInterior_isOpen H).interior_eq] at hzfront
        exact hzfront.2 hz
      · refine ⟨hzb,fun hzp => hzE (frontier_subset_closure (hf ▸ Or.inl hzp))⟩
    · rintro ⟨hzb,hzp⟩
      by_cases hzJ : z ∈ jordanInterior H
      · exact Or.inl hzJ
      · right
        refine ⟨?_,hzb⟩
        change z ∉ closure (jordanInterior H)
        rw [closure_eq_self_union_frontier]
        rintro (hz | hz)
        · exact hzJ hz
        · have h := hfront ▸ (show z ∈ frontier (jordanInterior H) ∩ ball 0 1 from ⟨hz,hzb⟩)
          exact hzp h.1
  · rw [frontier_inter_open_inter isOpen_ball,hEf,hfront]

end CircleDomainRigidity

end

end OAI
