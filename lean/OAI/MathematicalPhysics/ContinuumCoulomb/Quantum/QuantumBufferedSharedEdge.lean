import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedIntersections
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedGridEdge

namespace OAI

/-! Different routes do not share lattice edges, including at buffered endpoint cells. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSquareGrid_not_eightfold {p q : ℕ × ℕ}
    (hp : p.1 % 8 = 0 ∧ p.2 % 8 = 0) (hq : q.1 % 8 = 0 ∧ q.2 % 8 = 0) :
    ¬qmaSquareGrid.Adj p q := by
  intro h
  change Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 at h
  unfold Nat.dist at h
  omega

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem spaced_incident_support (v : Fin M.n) (e : M.Incident v) :
    M.spacedSupport e.val (qmaLanePoint (M.spacedColor e.val) (M.routeVertex v)) := by
  rcases e.property with h | h
  · left
    dsimp [spacedSupport,qmaLaneSupport,routeLeft,routeRight,routeVertex]
    rw [h]
    exact ⟨rfl,min_le_left _ _,le_max_left _ _⟩
  · right
    dsimp [spacedSupport,qmaLaneSupport,routeLeft,routeRight,routeVertex]
    rw [h]
    exact ⟨rfl,min_le_right _ _,le_max_right _ _⟩

theorem arm_lane_not_grid (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {f : M.Term} (hef : e.val ≠ f) {p : ℕ × ℕ}
    (he : M.endpointArmSupport hd v e p) (hf : M.spacedSupport f p) :
    ¬(p.1 % 8 = 0 ∧ p.2 % 8 = 0) := by
  intro hp
  have ht := M.endpointArmSupport_grid hd v e he hp
  have hg : M.spacedSupport e.val p := by rw [ht]; exact M.spaced_incident_support v e
  exact M.spaced_crossing_not_vertex hA hef hg hf e.val (M.routeVertex v) ht

theorem spaced_unit_direction (e : M.Term) {p q : ℕ × ℕ}
    (hp : M.spacedSupport e p) (hq : M.spacedSupport e q) (ha : qmaSquareGrid.Adj p q) :
    (p.1 = q.1 ∧ p.1 % 8 = 0) ∨ (p.2 = q.2 ∧ p.2 % 8 = 0) := by
  have haxis : p.1 = q.1 ∨ p.2 = q.2 := by
    change Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 at ha
    unfold Nat.dist at ha
    omega
  have hxm : (qmaLanePoint (M.spacedColor e) (qmaFineGridNat (M.routeRight e))).1 % 8 = 0 := by
    simp [qmaLanePoint,spacedColor,qmaSpacedLaneColor,Nat.add_mod,Nat.mul_mod]
  have hym : (qmaLanePoint (M.spacedColor e) (qmaFineGridNat (M.routeLeft e))).2 % 8 = 0 := by
    simp [qmaLanePoint,spacedColor,qmaSpacedLaneColor,Nat.add_mod,Nat.mul_mod]
  rcases hp with ⟨hpy,_⟩ | ⟨hpx,_⟩ <;> rcases hq with ⟨hqy,_⟩ | ⟨hqx,_⟩
  · exact Or.inr ⟨hpy.trans hqy.symm,by rw [hpy]; exact hym⟩
  · rcases haxis with hx | hy
    · exact Or.inl ⟨hx,by rw [hx,hqx]; exact hxm⟩
    · exact Or.inr ⟨hy,by rw [hpy]; exact hym⟩
  · rcases haxis with hx | hy
    · exact Or.inl ⟨hx,by rw [hpx]; exact hxm⟩
    · exact Or.inr ⟨hy,by rw [hy,hqy]; exact hym⟩
  · exact Or.inl ⟨hpx.trans hqx.symm,by rw [hpx]; exact hxm⟩

theorem endpointArm_lane_no_edge (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {f : M.Term} (hef : e.val ≠ f) {p q : ℕ × ℕ}
    (hp : M.endpointArmSupport hd v e p) (hq : M.endpointArmSupport hd v e q)
    (hpf : M.spacedSupport f p) (hqf : M.spacedSupport f q) (ha : qmaSquareGrid.Adj p q) : False := by
  obtain ⟨r,hr,hrs⟩ := hp
  obtain ⟨s,hs,hss⟩ := hq
  have har : qmaSquareGrid.Adj r s := by
    rw [← hr,← hs] at ha
    simpa only [qmaSquareGrid,qmaBufferedCellPoint,Nat.dist_add_add_left] using ha
  rcases M.spaced_unit_direction f hpf hqf ha with ⟨hxy,hm⟩ | ⟨hxy,hm⟩
  · have hx : r.1 = s.1 := by
      have h := congrArg Prod.fst hr
      have h' := congrArg Prod.fst hs
      dsimp [qmaBufferedCellPoint] at h h'
      omega
    have hm' : r.1 % 8 = 0 := by
      have h := congrArg (fun x : ℕ × ℕ => x.1 % 8) hr
      simpa [qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hm] using h
    have hd' : Nat.dist r.2 s.2 = 1 := by simpa [qmaSquareGrid,hx] using har
    rcases qmaBufferedFanout_vertical_grid_edge _ _ hrs hss hx hm' hd' with ht | ht
    · apply M.arm_lane_not_grid hA hd v e hef ⟨r,hr,hrs⟩ hpf
      simp [← hr,qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hm',ht]
    · apply M.arm_lane_not_grid hA hd v e hef ⟨s,hs,hss⟩ hqf
      simp [← hs,qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,← hx,hm',ht]
  · have hy : r.2 = s.2 := by
      have h := congrArg Prod.snd hr
      have h' := congrArg Prod.snd hs
      dsimp [qmaBufferedCellPoint] at h h'
      omega
    have hm' : r.2 % 8 = 0 := by
      have h := congrArg (fun x : ℕ × ℕ => x.2 % 8) hr
      simpa [qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hm] using h
    have hd' : Nat.dist r.1 s.1 = 1 := by simpa [qmaSquareGrid,hy] using har
    rcases qmaBufferedFanout_horizontal_grid_edge _ _ hrs hss hy hm' hd' with ht | ht
    · apply M.arm_lane_not_grid hA hd v e hef ⟨r,hr,hrs⟩ hpf
      simp [← hr,qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hm',ht]
    · apply M.arm_lane_not_grid hA hd v e hef ⟨s,hs,hss⟩ hqf
      simp [← hs,qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,← hy,hm',ht]


theorem bufferedPath_edge_piece (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {p q : ℕ × ℕ} (he : s(p,q) ∈ (M.bufferedPath hd e).val.edges) :
    (∃ (v : Fin M.n) (h : M.left e = v ∨ M.right e = v),
      M.endpointArmSupport hd v ⟨e,h⟩ p ∧ M.endpointArmSupport hd v ⟨e,h⟩ q) ∨
      (M.spacedSupport e p ∧ M.spacedSupport e q) := by
  have h := (M.bufferedWalk hd e).edges_toPath_subset_edges he
  simp only [bufferedWalk,SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_reverse,
    List.mem_append,List.mem_reverse] at h
  rcases h with (h | h) | h
  · exact Or.inl ⟨M.left e,Or.inl rfl,
      M.endpointArmWalk_support hd _ _ ((M.endpointArmWalk hd _ _).fst_mem_support_of_mem_edges h),
      M.endpointArmWalk_support hd _ _ ((M.endpointArmWalk hd _ _).snd_mem_support_of_mem_edges h)⟩
  · exact Or.inr ⟨M.spacedWalk_support e ((M.spacedWalk e).fst_mem_support_of_mem_edges h),
      M.spacedWalk_support e ((M.spacedWalk e).snd_mem_support_of_mem_edges h)⟩
  · exact Or.inl ⟨M.right e,Or.inr rfl,
      M.endpointArmWalk_support hd _ _ ((M.endpointArmWalk hd _ _).fst_mem_support_of_mem_edges h),
      M.endpointArmWalk_support hd _ _ ((M.endpointArmWalk hd _ _).snd_mem_support_of_mem_edges h)⟩

theorem bufferedPath_no_shared_edge (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {e f : M.Term} (hef : e ≠ f)
    {p q : ℕ × ℕ} (he : s(p,q) ∈ (M.bufferedPath hd e).val.edges)
    (hf : s(p,q) ∈ (M.bufferedPath hd f).val.edges) : False := by
  have ha := (M.bufferedPath hd e).val.adj_of_mem_edges he
  rcases M.bufferedPath_edge_piece hd e he with ⟨v,hv,hpe,hqe⟩ | ⟨hpe,hqe⟩ <;>
    rcases M.bufferedPath_edge_piece hd f hf with ⟨w,hw,hpf,hqf⟩ | ⟨hpf,hqf⟩
  · have hp := M.endpointArmSupport_meet hA hd v w ⟨e,hv⟩ ⟨f,hw⟩ hpe hpf
    have hq := M.endpointArmSupport_meet hA hd v w ⟨e,hv⟩ ⟨f,hw⟩ hqe hqf
    have hp' : p = M.placedVertex v := hp.resolve_left hef
    have hq' : q = M.placedVertex v := hq.resolve_left hef
    rw [hp',hq'] at ha
    exact qmaSquareGrid.irrefl ha
  · exact M.endpointArm_lane_no_edge hA hd v ⟨e,hv⟩ hef hpe hqe hpf hqf ha
  · exact M.endpointArm_lane_no_edge hA hd w ⟨f,hw⟩ hef.symm hpf hqf hpe hqe ha
  · exact qmaSquareGrid_not_eightfold (M.spaced_crossing_grid hA hef hpe hpf)
      (M.spaced_crossing_grid hA hef hqe hqf) ha

theorem bufferedPath_edge_disjoint (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {e f : M.Term} (hef : e ≠ f) :
    Disjoint (M.bufferedPath hd e).val.edgeSet (M.bufferedPath hd f).val.edgeSet := by
  apply Set.disjoint_left.mpr
  intro z he hf
  induction z using Sym2.inductionOn with
  | _ p q => exact M.bufferedPath_no_shared_edge hA hd hef he hf

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
