import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleRelabel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRoutePreservation
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPackedSchedule

namespace OAI

/-! The literal coordinate tape follows the canonical physical subdivision,
with a finite relabeling accounting for each emitted edge order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open scoped Classical
open QuantumListSchedule

theorem iterate_matches {Γ : SimpleGraph (ℕ × ℕ)} (N : ℚ) (s : State)
    (hs : Valid s.1) (P : QMAPathEmbedding (schedule s.1 hs) Γ)
    (hP : Represents s hs P) {T : QMAPathSchedule} (Q : QMAPathEmbedding T Γ)
    (E : QMAPathRelabeling (schedule s.1 hs) T)
    (hpos : ∀ v, Q.position (E.vertex v)=P.position v)
    (hpoint : ∀ e j, Q.point (E.edge e) j=P.point e j) (k : ℕ) :
    ∃ (hk : Valid (iterate N k s).1)
      (Pk : QMAPathEmbedding (schedule (iterate N k s).1 hk) Γ)
      (Ek : QMAPathRelabeling (schedule (iterate N k s).1 hk) (T.iterate N k)),
      Represents (iterate N k s) hk Pk ∧
      (∀ v, (Q.iterate N k).position (Ek.vertex v)=Pk.position v) ∧
      (∀ e j, (Q.iterate N k).point (Ek.edge e) j=Pk.point e j) := by
  induction k with
  | zero => exact ⟨hs,P,E,hP,hpos,hpoint⟩
  | succ k ih =>
    obtain ⟨hk,Pk,Ek,hPk,hvk,hek⟩ := ih
    let F := nextRelabel (N,(iterate N k s).1) hk
    refine ⟨value_valid (N,(iterate N k s).1) hk,
      nextEmbedding (N,(iterate N k s).1) hk Pk,F.trans (Ek.next N),
      value_represents (N,iterate N k s) hk Pk hPk,?_,?_⟩
    · intro v
      exact (Ek.next_position Pk (Q.iterate N k) hvk hek N (F.vertex v)).trans (by rfl)
    · intro e j
      exact (Ek.next_point Pk (Q.iterate N k) hek N (F.edge e) j).trans (by rfl)

theorem packed_matches (G : QMARationalExchangeGraph) {m : ℕ}
    (labels : G.Edge ≃ Fin m) (work : G.Edge → ℕ)
    {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding ⟨G,work⟩ Γ) (N : ℚ) (k : ℕ) :
    ∃ (hk : Valid (iterate N k (QuantumPackedSchedule.layout G labels work P)).1)
      (Pk : QMAPathEmbedding
        (schedule (iterate N k (QuantumPackedSchedule.layout G labels work P)).1 hk) Γ)
      (Ek : QMAPathRelabeling
        (schedule (iterate N k (QuantumPackedSchedule.layout G labels work P)).1 hk)
        ((QMAPathSchedule.mk G work).iterate N k)),
      Represents (iterate N k (QuantumPackedSchedule.layout G labels work P)) hk Pk ∧
      (∀ v, (P.iterate N k).position (Ek.vertex v)=Pk.position v) ∧
      (∀ e j, (P.iterate N k).point (Ek.edge e) j=Pk.point e j) := by
  exact iterate_matches N _ (QuantumPackedSchedule.valid G labels work)
    ((QuantumPackedSchedule.scheduleRelabel G labels work).symm.transport P)
    (QuantumPackedSchedule.layout_represents G labels work P) P
    (QuantumPackedSchedule.scheduleRelabel G labels work) (fun _ => rfl) (fun _ _ => rfl) k

theorem packed_matches_of_eq (G : QMARationalExchangeGraph) {m : ℕ}
    (labels : G.Edge ≃ Fin m) (work : G.Edge → ℕ)
    {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding ⟨G,work⟩ Γ) (N : ℚ) (k : ℕ) (s : State)
    (hs : s=QuantumPackedSchedule.layout G labels work P) :
    ∃ (hk : Valid (iterate N k s).1)
      (Pk : QMAPathEmbedding
        (schedule (iterate N k s).1 hk) Γ)
      (Ek : QMAPathRelabeling
        (schedule (iterate N k s).1 hk)
        ((QMAPathSchedule.mk G work).iterate N k)),
      Represents (iterate N k s) hk Pk ∧
      (∀ v, (P.iterate N k).position (Ek.vertex v)=Pk.position v) ∧
      (∀ e j, (P.iterate N k).point (Ek.edge e) j=Pk.point e j) := by
  subst s
  exact packed_matches G labels work P N k

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
