import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedSupport

namespace OAI

/-! Buffered arms are mutually disjoint away from their common graph vertex. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaBufferedCellPoint_injective (C : ℕ) (p : ℕ × ℕ) :
    Function.Injective (qmaBufferedCellPoint C p) := by
  intro x y h
  apply Prod.ext
  · exact Nat.add_left_cancel (congrArg Prod.fst h)
  · exact Nat.add_left_cancel (congrArg Prod.snd h)

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem endpointLocal_bounds (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (a : Fin 3) {p : ℕ × ℕ}
    (hs : qmaBufferedFanoutSupport (M.endpointColors hd v) (fun _ => false) a p) :
    0 < p.1 ∧ p.1 < 8*(9*B+9) ∧ 0 < p.2 ∧ p.2 < 8*(9*B+9) :=
  qmaBufferedFanout_bounded (M.endpointColors hd v)
    ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
    ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
    ((M.endpointPorts hd v).slot 2).isLt (fun _ => false) a hs

theorem endpointArmSupport_meet (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v w : Fin M.n) (e : M.Incident v) (f : M.Incident w) {z : ℕ × ℕ}
    (he : M.endpointArmSupport hd v e z) (hf : M.endpointArmSupport hd w f z) :
    e.val = f.val ∨ z = M.placedVertex v := by
  obtain ⟨p,hp,hps⟩ := he
  obtain ⟨q,hq,hqs⟩ := hf
  have hpb := M.endpointLocal_bounds hd v _ hps
  have hqb := M.endpointLocal_bounds hd w _ hqs
  have heq := hp.trans hq.symm
  have hvw : v = w := by
    apply M.routeVertex_injective
    by_contra hn
    exact qmaBufferedCellPoint_disjoint hn ⟨hpb.2.1,hpb.2.2.2⟩ ⟨hqb.2.1,hqb.2.2.2⟩ heq
  subst w
  have hpq := qmaBufferedCellPoint_injective (9*B+3) (M.routeVertex v) heq
  subst q
  by_cases hef : e.val = f.val
  · exact Or.inl hef
  · have ha : (M.endpointPorts hd v).assign e ≠ (M.endpointPorts hd v).assign f := by
      intro h
      exact hef (congrArg Subtype.val (M.endpointPorts_assign_injective hA hd v h))
    have hc := qmaBufferedFanout_only_center (M.endpointColors hd v)
      ((M.endpointPorts hd v).increasing (show (0 : Fin 3) < 1 by decide))
      ((M.endpointPorts hd v).increasing (show (1 : Fin 3) < 2 by decide))
      (fun _ => false) ha hps hqs
    exact Or.inr (hp.symm.trans (congrArg (qmaBufferedCellPoint (9*B+3) (M.routeVertex v)) hc))

theorem endpointArmSupport_grid (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) {z : ℕ × ℕ}
    (he : M.endpointArmSupport hd v e z) (hz : z.1 % 8 = 0 ∧ z.2 % 8 = 0) :
    z = qmaLanePoint (M.spacedColor e.val) (M.routeVertex v) := by
  obtain ⟨p,hp,hs⟩ := he
  have hx : p.1 % 8 = 0 := by
    have h := congrArg (fun z : ℕ × ℕ => z.1 % 8) hp
    simpa [qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hz.1] using h
  have hy : p.2 % 8 = 0 := by
    have h := congrArg (fun z : ℕ × ℕ => z.2 % 8) hp
    simpa [qmaBufferedCellPoint,Nat.add_mod,Nat.mul_mod,hz.2] using h
  have hx' : 8*(p.1/8) = p.1 := by omega
  have hy' : 8*(p.2/8) = p.2 := by omega
  have hg := qmaBufferedFanout_grid_point (M.endpointColors hd v) (fun _ => false)
    ((M.endpointPorts hd v).assign e) (p.1/8) (p.2/8) (by simpa only [hx',hy'] using hs)
  have hg' : p = (qmaBufferedPort (M.endpointColors hd v) ((M.endpointPorts hd v).assign e),
      qmaBufferedPort (M.endpointColors hd v) ((M.endpointPorts hd v).assign e)) := by
    simpa only [hx',hy'] using hg
  rw [hg'] at hp
  have halign := M.endpointArm_last hd v e
  simp only [endpointArmPoint,endpointArmLength,qmaBufferedArm_last] at halign
  exact hp.symm.trans halign

theorem spaced_crossing_grid (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (he : M.spacedSupport e z) (hf : M.spacedSupport f z) :
    z.1 % 8 = 0 ∧ z.2 % 8 = 0 := by
  have hc : M.spacedColor e ≠ M.spacedColor f := fun h =>
    Set.disjoint_left.mp (M.spaced_color_disjoint hA hef h) he hf
  rcases qmaLaneSupport_transverse hc he hf with ⟨hy,hx⟩ | ⟨hx,hy⟩
  all_goals
    constructor
    · rw [hx]
      simp [spacedColor,qmaSpacedLaneColor,Nat.add_mod,Nat.mul_mod]
    · rw [hy]
      simp [spacedColor,qmaSpacedLaneColor,Nat.add_mod,Nat.mul_mod]

theorem endpointArm_avoids_crossing (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (g : M.Incident v) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (he : M.spacedSupport e z) (hf : M.spacedSupport f z) :
    ¬M.endpointArmSupport hd v g z := by
  intro hg
  exact M.spaced_crossing_not_vertex hA hef he hf g.val (M.routeVertex v)
    (M.endpointArmSupport_grid hd v g hg (M.spaced_crossing_grid hA hef he hf))

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
