import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedEndpointWalk

namespace OAI

/-! The routed paths visit original graph vertices only at their own endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem routeVertex_injective : Function.Injective M.routeVertex := by
  intro v w h
  exact M.qubitSlots.site_injective (qmaFineGridNat_injective h)

theorem placedVertex_injective : Function.Injective M.placedVertex := by
  intro v w h
  have hh := congrArg (fun z : ℕ × ℕ =>
    (z.1/(8*(9*B+3+6)),z.2/(8*(9*B+3+6)))) h
  dsimp only [placedVertex] at hh
  rw [qmaBufferedCellPoint_cell (9*B+3) _ (17,17) (by omega) (by omega),
    qmaBufferedCellPoint_cell (9*B+3) _ (17,17) (by omega) (by omega)] at hh
  exact M.routeVertex_injective hh

def endpointArmSupport (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) (z : ℕ × ℕ) : Prop :=
  ∃ p, qmaBufferedCellPoint (9*B+3) (M.routeVertex v) p = z ∧
    qmaBufferedFanoutSupport (M.endpointColors hd v) (fun _ => false)
      ((M.endpointPorts hd v).assign e) p

theorem endpointArmWalk_support (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {z : ℕ × ℕ}
    (hz : z ∈ (M.endpointArmWalk hd v e).support) : M.endpointArmSupport hd v e z := by
  simp only [endpointArmWalk,SimpleGraph.Walk.support_copy] at hz
  obtain ⟨k,_,hk⟩ := qmaGridWalk_support _ _ _ hz
  exact ⟨_,hk,qmaBufferedArm_support _ _ _ k⟩

theorem endpointArmSupport_vertex (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v w : Fin M.n) (e : M.Incident v)
    (hz : M.endpointArmSupport hd v e (M.placedVertex w)) : v = w := by
  obtain ⟨p,hp,hs⟩ := hz
  have hb := qmaBufferedFanout_bounded (M.endpointColors hd v)
    ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
    ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
    ((M.endpointPorts hd v).slot 2).isLt (fun _ => false) _ hs
  apply M.routeVertex_injective
  have hh := congrArg (fun z : ℕ × ℕ =>
    (z.1/(8*(9*B+3+6)),z.2/(8*(9*B+3+6)))) hp
  dsimp only [placedVertex] at hh
  rw [qmaBufferedCellPoint_cell (9*B+3) _ p hb.2.1 hb.2.2.2,
    qmaBufferedCellPoint_cell (9*B+3) _ (17,17) (by omega) (by omega)] at hh
  exact hh

theorem spacedSupport_not_vertex (e : M.Term) (v : Fin M.n) :
    ¬M.spacedSupport e (M.placedVertex v) := by
  intro h
  rcases h with ⟨h,_⟩ | ⟨h,_⟩
  all_goals
    have hm := congrArg (fun x : ℕ => x % 8) h
    simp [placedVertex,qmaBufferedCellPoint,qmaLanePoint,spacedColor,qmaSpacedLaneColor,
      Nat.add_mod,Nat.mul_mod] at hm

theorem spacedWalk_support (e : M.Term) {z : ℕ × ℕ}
    (hz : z ∈ (M.spacedWalk e).support) : M.spacedSupport e z := by
  simp only [spacedWalk,SimpleGraph.Walk.support_copy] at hz
  obtain ⟨k,hk,he⟩ := qmaGridWalk_support _ _ _ hz
  rw [← he]
  exact qmaManhattanPoint_support _ _ k hk

theorem bufferedPath_support (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {z : ℕ × ℕ} (hz : z ∈ (M.bufferedPath hd e).val.support) :
    M.endpointArmSupport hd (M.left e) ⟨e,Or.inl rfl⟩ z ∨ M.spacedSupport e z ∨
      M.endpointArmSupport hd (M.right e) ⟨e,Or.inr rfl⟩ z := by
  have h := (M.bufferedWalk hd e).support_toPath_subset_support hz
  simp only [bufferedWalk,SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse,List.mem_reverse] at h
  rcases h with (h | h) | h
  · exact Or.inl (M.endpointArmWalk_support hd _ _ h)
  · exact Or.inr (Or.inl (M.spacedWalk_support e h))
  · exact Or.inr (Or.inr (M.endpointArmWalk_support hd _ _ h))

theorem bufferedPath_vertex (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (v : Fin M.n) (hz : M.placedVertex v ∈ (M.bufferedPath hd e).val.support) :
    v = M.left e ∨ v = M.right e := by
  rcases M.bufferedPath_support hd e hz with h | h | h
  · exact Or.inl (M.endpointArmSupport_vertex hd _ _ _ h).symm
  · exact (M.spacedSupport_not_vertex e v h).elim
  · exact Or.inr (M.endpointArmSupport_vertex hd _ _ _ h).symm

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
