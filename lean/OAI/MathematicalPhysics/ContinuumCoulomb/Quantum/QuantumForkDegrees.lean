import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkSpectrum

namespace OAI

/-! The parallel fork graph halves the degree of its center. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaForkPortEquiv (d : ℕ) : (Fin (d/2) × Fin 2) ⊕ Fin (d%2) ≃ Fin d :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by omega))

abbrev QMAForkStarVertex (d : ℕ) := Unit ⊕ (Fin d ⊕ (Fin (d/2) × Fin 2))
abbrev QMAForkStarEdge (d : ℕ) :=
  Fin (d/2) ⊕ (Fin (d/2) ⊕ ((Fin (d/2) × Fin 2) ⊕ (Fin (d/2) ⊕ Fin (d%2))))

def qmaForkStarLeft (d : ℕ) : QMAForkStarEdge d → QMAForkStarVertex d
  | .inl i => .inr (.inr (i,0))
  | .inr (.inl _) => .inl ()
  | .inr (.inr (.inl p)) => .inr (.inl (qmaForkPortEquiv d (.inl p)))
  | .inr (.inr (.inr (.inl i))) => .inr (.inl (qmaForkPortEquiv d (.inl (i,0))))
  | .inr (.inr (.inr (.inr _))) => .inl ()

def qmaForkStarRight (d : ℕ) : QMAForkStarEdge d → QMAForkStarVertex d
  | .inl i => .inr (.inr (i,1))
  | .inr (.inl i) => .inr (.inr (i,0))
  | .inr (.inr (.inl p)) => .inr (.inr (p.1,1))
  | .inr (.inr (.inr (.inl i))) => .inr (.inl (qmaForkPortEquiv d (.inl (i,1))))
  | .inr (.inr (.inr (.inr k))) => .inr (.inl (qmaForkPortEquiv d (.inr k)))

def qmaForkStarDegree (d : ℕ) (v : QMAForkStarVertex d) : ℕ :=
  ∑ e, if qmaForkStarLeft d e = v ∨ qmaForkStarRight d e = v then 1 else 0

theorem qmaForkStar_center_degree (d : ℕ) : qmaForkStarDegree d (.inl ()) = d/2+d%2 := by
  simp [qmaForkStarDegree,qmaForkStarLeft,qmaForkStarRight,Fintype.sum_sum_type]

theorem qmaForkStar_center_decreases (d : ℕ) (hd : 2 ≤ d) :
    qmaForkStarDegree d (.inl ()) < d := by
  rw [qmaForkStar_center_degree]
  omega

theorem qmaForkStar_no_loops (d : ℕ) (e : QMAForkStarEdge d) :
    qmaForkStarLeft d e ≠ qmaForkStarRight d e := by
  rcases e with i | e
  · simp [qmaForkStarLeft,qmaForkStarRight]
  rcases e with i | e
  · simp [qmaForkStarLeft,qmaForkStarRight]
  rcases e with p | e
  · simp [qmaForkStarLeft,qmaForkStarRight]
  rcases e with i | k
  · intro h
    have hp := (qmaForkPortEquiv d).injective (Sum.inl.inj (Sum.inr.inj h))
    have hbit := congrArg Prod.snd (Sum.inl.inj hp)
    norm_num at hbit
  · simp [qmaForkStarLeft,qmaForkStarRight]

theorem qmaForkStar_new_degree (d : ℕ) (i : Fin (d/2)) (b : Fin 2) :
    qmaForkStarDegree d (.inr (.inr (i,b))) = if b = 0 then 2 else 3 := by
  simp only [qmaForkStarDegree,Fintype.sum_sum_type,Fintype.sum_prod_type,
    qmaForkStarLeft,qmaForkStarRight]
  fin_cases b <;> simp

theorem qmaForkStar_paired_degree (d : ℕ) (i : Fin (d/2)) (b : Fin 2) :
    qmaForkStarDegree d (.inr (.inl (qmaForkPortEquiv d (.inl (i,b))))) = 2 := by
  fin_cases b <;>
    simp [qmaForkStarDegree,qmaForkStarLeft,qmaForkStarRight,Fintype.sum_sum_type]

theorem qmaForkStar_leftover_degree (d : ℕ) (i : Fin (d%2)) :
    qmaForkStarDegree d (.inr (.inl (qmaForkPortEquiv d (.inr i)))) = 1 := by
  simp [qmaForkStarDegree,qmaForkStarLeft,qmaForkStarRight,Fintype.sum_sum_type]

theorem qmaForkStar_noncenter_degree (d : ℕ) (v : QMAForkStarVertex d)
    (hv : v ≠ .inl ()) : qmaForkStarDegree d v ≤ 3 := by
  rcases v with u | v
  · cases u; exact (hv rfl).elim
  rcases v with j | p
  · obtain ⟨q,hq⟩ := (qmaForkPortEquiv d).surjective j
    subst j
    rcases q with p | k
    · rw [qmaForkStar_paired_degree]; omega
    · rw [qmaForkStar_leftover_degree]; omega
  · rw [qmaForkStar_new_degree]
    split <;> omega

theorem qmaForkStar_vertex_count (d : ℕ) :
    Fintype.card (QMAForkStarVertex d) = 1+d+2*(d/2) := by
  simp [QMAForkStarVertex,Fintype.card_sum,Fintype.card_prod]
  omega

theorem qmaForkStar_edge_count (d : ℕ) :
    Fintype.card (QMAForkStarEdge d) = 5*(d/2)+d%2 := by
  simp [QMAForkStarEdge,Fintype.card_sum,Fintype.card_prod]
  omega

/-- A constant degree bound permits a constant number of fork rounds. -/
def qmaForkDegreeAfter (d : ℕ) : ℕ → ℕ
  | 0 => d
  | k+1 => qmaForkDegreeAfter d k / 2 + qmaForkDegreeAfter d k % 2

theorem qmaForkDegreeAfter_bound (d k : ℕ) :
    qmaForkDegreeAfter d k ≤ max 1 (d-k) := by
  induction k with
  | zero => simp [qmaForkDegreeAfter]
  | succ k ih =>
    simp only [qmaForkDegreeAfter]
    by_cases h : qmaForkDegreeAfter d k ≤ 1
    · have hf : qmaForkDegreeAfter d k / 2 + qmaForkDegreeAfter d k % 2 ≤ 1 := by omega
      exact hf.trans (le_max_left _ _)
    · have hf : qmaForkDegreeAfter d k / 2 + qmaForkDegreeAfter d k % 2 <
          qmaForkDegreeAfter d k := by omega
      omega

theorem qmaForkDegreeAfter_constant (d D : ℕ) (hd : d ≤ D) :
    qmaForkDegreeAfter d D ≤ 1 := by
  have h := qmaForkDegreeAfter_bound d D
  simpa [Nat.sub_eq_zero_of_le hd] using h

end ContinuumCoulomb

end

end OAI
