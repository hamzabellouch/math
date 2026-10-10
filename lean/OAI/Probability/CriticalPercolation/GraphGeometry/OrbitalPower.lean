import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def powerOn (O : Set V) (L : ℕ) : SimpleGraph O where
  Adj u v := u≠v ∧ v.val∈G.vertexBall u.val L
  symm := ⟨fun _ _ h => ⟨h.1.symm,G.vertexBall_comm.mp h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma powerOn_reachable_of_close {O : Set V} {L : ℕ} (u v : O)
    (h : v.val∈G.vertexBall u.val L) : (G.powerOn O L).Reachable u v := by
  by_cases huv : u=v
  · rw [huv]
  · exact SimpleGraph.Adj.reachable (⟨huv,h⟩ : (G.powerOn O L).Adj u v)

lemma powerOn_reachable_lift {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C)
    {x y : V} (p : G.fullGraph.Walk x y) (u v : O)
    (hu : u.val∈G.vertexBall x C) (hv : v.val∈G.vertexBall y C) :
    (G.powerOn O (2*C+1)).Reachable u v := by
  induction p generalizing u with
  | nil =>
    apply G.powerOn_reachable_of_close
    exact G.vertexBall_mono u.val (by omega)
      (G.vertexBall_add (G.vertexBall_comm.mp hu) C hv)
  | @cons x z y hxz p ih =>
    obtain ⟨w,hw⟩ := hdense z
    apply SimpleGraph.Reachable.trans (v := w)
    · apply G.powerOn_reachable_of_close
      have hz := G.vertexBall_step (G.vertexBall_comm.mp hu) hxz
      have hvw := G.vertexBall_add hz C hw
      simpa only [show C+1+C=2*C+1 by omega] using hvw
    · exact ih w hw hv

lemma powerOn_connected (hc : G.fullGraph.Connected) {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C) :
    (G.powerOn O (2*C+1)).Connected := by
  let _ := hc.nonempty
  obtain ⟨o⟩ := ‹Nonempty V›
  obtain ⟨u,_⟩ := hdense o
  let _ : Nonempty O := ⟨u⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨p⟩ := hc x.val y.val
  exact G.powerOn_reachable_lift hdense p x y
    (G.mem_vertexBall_self x.val C) (G.mem_vertexBall_self y.val C)

lemma powerOn_finite_neighbors (hl : G.LocallyFinite) (O : Set V) (L : ℕ) (u : O) :
    ((G.powerOn O L).neighborSet u).Finite := by
  apply (Set.Finite.preimage Subtype.val_injective.injOn (G.vertexBall_finite hl u.val L)).subset
  exact fun _ h => h.2

lemma powerOn_walk_bound {O : Set V} {L : ℕ} {u v : O}
    (p : (G.powerOn O L).Walk u v) :
    v.val∈G.vertexBall u.val (L*p.length) := by
  induction p with
  | nil => exact G.mem_vertexBall_self _ _
  | @cons u w v huw p ih =>
    simpa only [SimpleGraph.Walk.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm]
      using G.vertexBall_add huw.2 (L*p.length) ih

lemma powerOn_ball_bound {O : Set V} {L n : ℕ} (u : O) :
    {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n} ⊆
      Subtype.val ⁻¹' G.vertexBall u.val (L*n) := by
  rintro v ⟨p,hp⟩
  exact G.vertexBall_mono u.val (Nat.mul_le_mul_left _ hp) (G.powerOn_walk_bound p)

lemma powerOn_ball_card_le (hl : G.LocallyFinite) {O : Set V} {L n C R : ℕ}
    (x : V) (u : O) (hu : u.val∈G.vertexBall x C) (hR : C+L*n≤R) :
    {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n}.ncard ≤
      (G.vertexBall x R).ncard := by
  have hh : {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n} ⊆
      Subtype.val ⁻¹' G.vertexBall x R := by
    intro v hv
    exact G.vertexBall_mono x hR (G.vertexBall_add hu (L*n) (G.powerOn_ball_bound u hv))
  calc
    _ = (Subtype.val '' {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n}).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.vertexBall x R).ncard := Set.ncard_le_ncard (Set.image_subset_iff.mpr hh)
      (G.vertexBall_finite hl x R)

end CriticalPercolation.BondGraph
end
end
end

end OAI
