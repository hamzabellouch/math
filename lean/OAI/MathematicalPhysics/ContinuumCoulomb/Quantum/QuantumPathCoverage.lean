import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutedSubdivision

namespace OAI

/-! Every prescribed path point becomes an actual spin when subdivision finishes. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

theorem next_covers_point (N : ℚ) (e : W.graph.Edge) (k : ℕ) (hk : k ≤ 2*W.work e+1) :
    ∃ (f : (W.next N).graph.Edge) (l : ℕ), l ≤ 2*(W.next N).work f+1 ∧
      (P.next N).point f l = P.point e k := by
  by_cases he : e ∈ W.active
  · let i : Fin W.active.card := W.active.equivFin ⟨e,he⟩
    have hi : qmaSelectedIndex W.active i = e := by simp [qmaSelectedIndex,i]
    have hw : 0 < W.work e := (W.mem_active e).mp he
    by_cases hk1 : k ≤ 1
    · refine ⟨Sum.inr (Sum.inr (i,0)),k,?_,?_⟩
      · exact hk1
      · change P.point (qmaSelectedIndex W.active i) k = _
        rw [hi]
    by_cases hk2 : k = 2
    · subst k
      refine ⟨Sum.inr (Sum.inl i),1,by exact Nat.le_refl 1,?_⟩
      change P.point (qmaSelectedIndex W.active i) (1+1) = _
      rw [hi]
    · refine ⟨Sum.inr (Sum.inr (i,1)),2*W.work e+1-k,?_,?_⟩
      · change 2*W.work e+1-k ≤ 2*(W.work (qmaSelectedIndex W.active i)-1)+1
        rw [hi]
        omega
      · change P.point (qmaSelectedIndex W.active i)
          (2*W.work (qmaSelectedIndex W.active i)+1-(2*W.work e+1-k)) = _
        rw [hi]
        congr 1
        omega
  · refine ⟨Sum.inl ⟨e,he⟩,k,?_,rfl⟩
    have hle : W.work e ≤ 0 := by simpa only [W.mem_active,not_lt] using he
    have hw : W.work e = 0 := Nat.eq_zero_of_le_zero hle
    change k ≤ 1
    simpa only [hw,Nat.mul_zero,Nat.zero_add] using hk

def Occupied (z : ℕ × ℕ) : Prop :=
  (∃ v, P.position v = z) ∨ ∃ e k, k ≤ 2*W.work e+1 ∧ P.point e k = z

theorem next_occupied (N : ℚ) {z : ℕ × ℕ} (hz : P.Occupied z) : (P.next N).Occupied z := by
  rcases hz with ⟨v,hv⟩ | ⟨e,k,hk,hz⟩
  · exact Or.inl ⟨old W.graph.n W.active.card v,(P.nextPosition_old v).trans hv⟩
  · obtain ⟨f,l,hl,he⟩ := P.next_covers_point N e k hk
    exact Or.inr ⟨f,l,hl,he.trans hz⟩

theorem iterate_occupied (N : ℚ) {z : ℕ × ℕ} (hz : P.Occupied z) (k : ℕ) :
    (P.iterate N k).Occupied z := by
  induction k with
  | zero => exact hz
  | succ k ih => exact (P.iterate N k).next_occupied N ih

theorem occupied_complete (h : ∀ e, W.work e = 0) {z : ℕ × ℕ} (hz : P.Occupied z) :
    ∃ v, P.position v = z := by
  rcases hz with hv | ⟨e,k,hk,hz⟩
  · exact hv
  have hk1 : k ≤ 1 := by simpa only [h e,Nat.mul_zero,Nat.zero_add] using hk
  by_cases hk0 : k = 0
  · subst k
    exact ⟨W.graph.left e,(P.first e).symm.trans hz⟩
  · have hk' : k = 1 := by omega
    have hl := P.last e
    simp only [h e,Nat.mul_zero,Nat.zero_add] at hl
    subst k
    exact ⟨W.graph.right e,hl.symm.trans hz⟩

theorem iterate_covers_point (N : ℚ) {D : ℕ} (hD : ∀ e, W.work e ≤ D)
    (e : W.graph.Edge) (k : ℕ) (hk : k ≤ 2*W.work e+1) :
    ∃ v, (P.iterate N D).position v = P.point e k :=
  (P.iterate N D).occupied_complete (W.iterate_complete N hD)
    (P.iterate_occupied N (Or.inr ⟨e,k,hk,rfl⟩) D)

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
