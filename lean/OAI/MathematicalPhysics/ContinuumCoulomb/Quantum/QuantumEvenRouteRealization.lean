import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenRoutePlacement

namespace OAI

/-! Full even-route realization from the reserved-leaf placement. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical
namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

def Bounded (X Y : ℕ) : Prop :=
  (∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y) ∧
  (∀ e k, k ≤ 2*P.work e+2 → (P.point e k).1 < X ∧ (P.point e k).2 < Y) ∧
  ∀ e, (P.leaf e).1 < X ∧ (P.leaf e).2 < Y

theorem embedding_bounded (N : ℚ) {X Y : ℕ} (h : P.Bounded X Y) :
    (P.embedding N).Bounded X Y := by
  constructor
  · change ∀ v : Fin (G.n+(Finset.univ : Finset G.Edge).card*2),
      (P.nextPosition v).1 < X ∧ (P.nextPosition v).2 < Y
    intro v
    obtain ⟨v,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective v
    rcases v with v | ⟨i,b⟩
    · change (P.nextPosition (old _ _ v)).1 < X ∧ (P.nextPosition (old _ _ v)).2 < Y
      simpa only [nextPosition_old] using h.1 v
    · change (P.nextPosition (fresh _ _ i b)).1 < X ∧ (P.nextPosition (fresh _ _ i b)).2 < Y
      rw [nextPosition_fresh]
      fin_cases b
      · exact h.2.1 (selected i) 1 (by omega)
      · exact h.2.2 (selected i)
  · intro e k hk
    change (P.nextPoint e k).1 < X ∧ (P.nextPoint e k).2 < Y
    rcases e with e | (i | ⟨i,a⟩)
    · exact (e.property (Finset.mem_univ _)).elim
    · change (if k = 0 then P.point (selected i) 1 else P.leaf (selected i)).1 < X ∧
        (if k = 0 then P.point (selected i) 1 else P.leaf (selected i)).2 < Y
      split
      · exact h.2.1 (selected i) 1 (by omega)
      · exact h.2.2 (selected i)
    · fin_cases a
      · have hk' : k ≤ 1 := hk
        exact h.2.1 (selected i) k (by omega)
      · exact h.2.1 (selected i) (2*P.work (selected i)+2-k) (Nat.sub_le _ _)

theorem schedule_degree (N : ℚ) {d : ℕ} (h3 : 3 ≤ d)
    (hd : ∀ v, qmaGraphDegree G.left G.right v ≤ d) :
    ∀ v, qmaGraphDegree (P.schedule N).graph.left (P.schedule N).graph.right v ≤ d := by
  intro v
  obtain ⟨v,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective v
  rcases v with v | ⟨i,b⟩
  · change qmaGraphDegree (qmaPartialPathsLeft G.left G.right Finset.univ)
      (qmaPartialPathsRight G.right Finset.univ (fun _ => true)) (old _ _ v) ≤ d
    rw [qmaPartialPaths_old_degree _ _ G.distinct]
    exact hd v
  · change qmaGraphDegree (qmaPartialPathsLeft G.left G.right Finset.univ)
      (qmaPartialPathsRight G.right Finset.univ (fun _ => true)) (fresh _ _ i b) ≤ d
    exact (qmaPartialPaths_fresh_degree _ _ _ _ i b).trans h3

theorem schedule_size (N : ℚ) :
    (P.schedule N).graph.n+Fintype.card (P.schedule N).graph.Edge ≤
      5*(G.n+Fintype.card G.Edge) := by
  change G.n+(Finset.univ : Finset G.Edge).card*2+
    Fintype.card (G.subdivide Finset.univ (fun _ => true) N).Edge ≤ _
  rw [QMARationalExchangeGraph.subdivide_edge_count]
  simp only [Finset.card_univ]
  omega

theorem realize {N : ℚ} (hN : 0 < N) {D X Y d : ℕ} (h3 : 3 ≤ d)
    (hD : ∀ e, P.work e ≤ D) (hbox : P.Bounded X Y)
    (hd : ∀ v, qmaGraphDegree G.left G.right v ≤ d) :
    ∃ (H : QMARationalExchangeGraph) (position : Fin H.n → ℕ × ℕ),
      Function.Injective position ∧
      (∀ v, (position v).1 < X ∧ (position v).2 < Y) ∧
      (∀ e, qmaSquareGrid.Adj (position (H.left e)) (position (H.right e))) ∧
      (∀ v, qmaGraphDegree H.left H.right v ≤ d) ∧
      H.n+Fintype.card H.Edge ≤ 5^(D+1)*(G.n+Fintype.card G.Edge) ∧
      |H.energy-G.energy| ≤ ((D+1:ℕ):ℝ)/(N:ℝ) := by
  obtain ⟨H,p,hp,hbox',ha,hd',hs,he⟩ := (P.embedding N).realize hN h3
    (P.schedule_work_le N hD) (P.embedding_bounded N hbox) (P.schedule_degree N h3 hd)
  refine ⟨H,p,hp,hbox',ha,hd',?_,?_⟩
  · exact hs.trans (by simpa [pow_succ,mul_assoc] using
      Nat.mul_le_mul_left (5^D) (P.schedule_size N))
  · calc
      _ ≤ |H.energy-(P.schedule N).graph.energy|+|(P.schedule N).graph.energy-G.energy| :=
        abs_sub_le _ _ _
      _ ≤ (D:ℝ)/(N:ℝ)+1/(N:ℝ) := add_le_add he (P.schedule_energy_error hN)
      _ = ((D+1:ℕ):ℝ)/(N:ℝ) := by push_cast; ring

end QMAEvenRouteData
end ContinuumCoulomb

end

end OAI
