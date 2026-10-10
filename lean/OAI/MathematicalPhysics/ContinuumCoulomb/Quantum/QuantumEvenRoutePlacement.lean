import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenRouteData

namespace OAI

/-! The even gadget places its interacting vertex at route point one and its
second singlet spin at the reserved leaf. The remaining routes have odd length. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

def nextPoint (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (k : ℕ) : ℕ × ℕ :=
  match e with
  | .inl e => P.point e.val k
  | .inr (.inl i) => if k = 0 then P.point (selected i) 1 else P.leaf (selected i)
  | .inr (.inr (i,a)) => if a = 0 then P.point (selected i) k
      else P.point (selected i) (2*P.work (selected i)+2-k)

theorem nextPoint_first (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) :
    P.nextPoint e 0 = P.nextPosition (qmaPartialPathsLeft G.left G.right Finset.univ e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · change P.point (selected i) 1 = P.nextPosition (fresh _ _ i 0)
    rw [nextPosition_fresh]
    rfl
  · fin_cases a
    · change P.point (selected i) 0 = P.nextPosition (old _ _ (G.left (selected i)))
      rw [nextPosition_old]
      exact P.first _
    · change P.point (selected i) (2*P.work (selected i)+2) =
        P.nextPosition (old _ _ (G.right (selected i)))
      rw [nextPosition_old]
      exact P.last _

theorem nextPoint_last (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) :
    P.nextPoint e (2*P.nextWork e+1) =
      P.nextPosition (qmaPartialPathsRight G.right Finset.univ (fun _ => true) e) := by
  rcases e with e | (i | ⟨i,a⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · change P.leaf (selected i) = P.nextPosition (fresh _ _ i 1)
    rw [nextPosition_fresh]
    rfl
  · fin_cases a
    · change P.point (selected i) 1 = P.nextPosition (fresh _ _ i 0)
      rw [nextPosition_fresh]
      rfl
    · change P.point (selected i) (2*P.work (selected i)+2-(2*P.work (selected i)+1)) =
        P.nextPosition (fresh _ _ i 0)
      rw [nextPosition_fresh]
      change P.point (selected i) _ = P.point (selected i) 1
      congr 1
      omega

theorem nextPoint_simple (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (i j : ℕ)
    (hi : i ≤ 2*P.nextWork e+1) (hj : j ≤ 2*P.nextWork e+1)
    (h : P.nextPoint e i = P.nextPoint e j) : i = j := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · simp only [nextWork,Nat.mul_zero,Nat.zero_add] at hi hj
    by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
    · omega
    · have hj1 : j = 1 := by omega
      subst i
      subst j
      exact (P.leaf_avoids (selected a) (selected a) 1 (by omega) h.symm).elim
    · have hi1 : i = 1 := by omega
      subst i
      subst j
      exact (P.leaf_avoids (selected a) (selected a) 1 (by omega) h).elim
    · omega
  · fin_cases b
    · simp [nextWork] at hi hj
      exact P.simple (selected a) i j (by omega) (by omega) h
    · simp [nextWork] at hi hj
      change P.point (selected a) (2*P.work (selected a)+2-i) =
        P.point (selected a) (2*P.work (selected a)+2-j) at h
      have he := P.simple (selected a) _ _ (Nat.sub_le _ _) (Nat.sub_le _ _) h
      omega

theorem nextPoint_step (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (i : ℕ)
    (hi : i < 2*P.nextWork e+1) : qmaSquareGrid.Adj (P.nextPoint e i) (P.nextPoint e (i+1)) := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · have hi0 : i = 0 := by simp [nextWork] at hi; omega
    subst i
    exact P.leaf_step (selected a)
  · fin_cases b
    · have hi0 : i = 0 := by simp [nextWork] at hi; omega
      subst i
      exact P.step (selected a) 0 (by omega)
    · simp [nextWork] at hi
      have hk : 2*P.work (selected a)+2-(i+1) < 2*P.work (selected a)+2 := by omega
      have he : 2*P.work (selected a)+2-i = (2*P.work (selected a)+2-(i+1))+1 := by omega
      change qmaSquareGrid.Adj (P.point (selected a) (2*P.work (selected a)+2-i))
        (P.point (selected a) (2*P.work (selected a)+2-(i+1)))
      rw [he]
      exact (P.step (selected a) _ hk).symm

theorem nextPoint_avoids (e : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (i : ℕ)
    (v : Fin (G.n+(Finset.univ : Finset G.Edge).card*2))
    (hi0 : 0 < i) (hi : i < 2*P.nextWork e+1) : P.nextPoint e i ≠ P.nextPosition v := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · simp [nextWork] at hi
    omega
  · fin_cases b
    · simp [nextWork] at hi
      omega
    simp [nextWork] at hi
    have hidx0 : 1 < 2*P.work (selected a)+2-i := by omega
    have hidx : 2*P.work (selected a)+2-i < 2*P.work (selected a)+2 := by omega
    obtain ⟨v,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective v
    rcases v with v | ⟨c,d⟩
    · change P.point (selected a) (2*P.work (selected a)+2-i) ≠ P.nextPosition (old _ _ v)
      rw [nextPosition_old]
      exact P.avoids _ _ v (by omega) hidx
    · change P.point (selected a) (2*P.work (selected a)+2-i) ≠ P.nextPosition (fresh _ _ c d)
      rw [nextPosition_fresh]
      fin_cases d
      · intro h
        by_cases he : selected a = selected c
        · change P.point (selected a) _ = P.point (selected c) 1 at h
          rw [← he] at h
          have hx := P.simple (selected a) _ 1 (Nat.sub_le _ _) (by omega) h
          omega
        · exact P.disjoint _ _ _ 1 he (by omega) hidx (by omega) h
      · intro h
        exact P.leaf_avoids (selected c) (selected a) _ (Nat.sub_le _ _) h.symm

theorem nextPoint_disjoint (e f : QMAPartialPathsEdge (Finset.univ : Finset G.Edge)) (i j : ℕ)
    (hef : e ≠ f) (hi0 : 0 < i) (hi : i < 2*P.nextWork e+1) (hj : j ≤ 2*P.nextWork f+1) :
    P.nextPoint e i ≠ P.nextPoint f j := by
  rcases e with e | (a | ⟨a,b⟩)
  · exact (e.property (Finset.mem_univ _)).elim
  · simp [nextWork] at hi
    omega
  · fin_cases b
    · simp [nextWork] at hi
      omega
    simp [nextWork] at hi
    have hidx0 : 1 < 2*P.work (selected a)+2-i := by omega
    have hidx : 2*P.work (selected a)+2-i < 2*P.work (selected a)+2 := by omega
    intro h
    rcases f with f | (c | ⟨c,d⟩)
    · exact (f.property (Finset.mem_univ _)).elim
    · by_cases hj0 : j = 0
      · change P.point (selected a) _ = (if j = 0 then P.point (selected c) 1 else _) at h
        simp only [hj0,ite_true] at h
        by_cases he : selected a = selected c
        · rw [← he] at h
          have hx := P.simple (selected a) _ 1 (Nat.sub_le _ _) (by omega) h
          omega
        · exact P.disjoint _ _ _ 1 he (by omega) hidx (by omega) h
      · change P.point (selected a) _ = (if j = 0 then _ else P.leaf (selected c)) at h
        simp only [hj0,ite_false] at h
        exact P.leaf_avoids (selected c) (selected a) _ (Nat.sub_le _ _) h.symm
    · fin_cases d
      · simp [nextWork] at hj
        change P.point (selected a) _ = P.point (selected c) j at h
        by_cases he : selected a = selected c
        · rw [← he] at h
          have hx := P.simple (selected a) _ j (Nat.sub_le _ _) (by omega) h
          omega
        · exact P.disjoint _ _ _ j he (by omega) hidx (by omega) h
      · simp [nextWork] at hj
        change P.point (selected a) _ = P.point (selected c) (2*P.work (selected c)+2-j) at h
        have he : selected a = selected c := by
          by_contra hn
          exact P.disjoint _ _ _ _ hn (by omega) hidx (Nat.sub_le _ _) h
        have hac := selected_injective he
        subst c
        exact hef rfl

def embedding (N : ℚ) : QMAPathEmbedding (P.schedule N) where
  position := P.nextPosition
  position_injective := P.nextPosition_injective
  point := P.nextPoint
  first := P.nextPoint_first
  last := P.nextPoint_last
  simple := P.nextPoint_simple
  step := P.nextPoint_step
  avoids := P.nextPoint_avoids
  disjoint := P.nextPoint_disjoint

end QMAEvenRouteData
end ContinuumCoulomb

end

end OAI
