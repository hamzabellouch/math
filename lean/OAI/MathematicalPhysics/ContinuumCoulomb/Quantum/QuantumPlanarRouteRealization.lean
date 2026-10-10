import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarRouteData

namespace OAI

/-! A bounded planar route family produces the actual nearest-neighbor rational
Hamiltonian with a fixed number of perturbative layers. -/

namespace ContinuumCoulomb

theorem qmaInflatedPoint_bounded (p : ℕ → ℕ × ℕ) {L X Y : ℕ}
    (hp : ∀ i < L, qmaSquareGrid.Adj (p i) (p (i+1)))
    (hb : ∀ i ≤ L, (p i).1 < X ∧ (p i).2 < Y) {k : ℕ} (hk : k ≤ 8*L) :
    (qmaInflatedPoint p k).1 < 8*X ∧ (qmaInflatedPoint p k).2 < 8*Y := by
  by_cases hz : k%8 = 0
  · rw [qmaInflatedPoint_boundary p hz]
    obtain ⟨hx,hy⟩ := hb (k/8) (by omega)
    simp only [qmaLeafCenter]
    omega
  · have hd : k/8 < L := by omega
    have hl := qmaLeafCenter_adj_length (hp _ hd)
    have hi : k%8 ≤ qmaManhattanLength (qmaLeafCenter (p (k/8)))
        (qmaLeafCenter (p (k/8+1))) := by omega
    have hh := qmaManhattanPoint_bounds _ _ _ hi
    obtain ⟨hx,hy⟩ := hb (k/8) hd.le
    obtain ⟨hx',hy'⟩ := hb (k/8+1) (by omega)
    change (qmaManhattanPoint _ _ _).1 < _ ∧ (qmaManhattanPoint _ _ _).2 < _
    simp only [qmaLeafCenter] at hh
    constructor
    · exact hh.2.1.trans_lt (max_lt (by omega) (by omega))
    · exact hh.2.2.2.trans_lt (max_lt (by omega) (by omega))

noncomputable section
open scoped Classical
namespace QMAPlanarRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)

def Bounded (X Y : ℕ) : Prop :=
  (∀ v, (P.position v).1 < X ∧ (P.position v).2 < Y) ∧
  ∀ e i, i ≤ P.length e → (P.point e i).1 < X ∧ (P.point e i).2 < Y

theorem toEven_bounded {X Y : ℕ} (hb : P.Bounded X Y) : P.toEven.Bounded (8*X) (8*Y) := by
  refine ⟨?_,?_,?_⟩
  · intro v
    obtain ⟨hx,hy⟩ := hb.1 v
    change 8*(P.position v).1+4 < 8*X ∧ 8*(P.position v).2+4 < 8*Y
    omega
  · intro e k hk
    change k ≤ 2*(4*P.length e-1)+2 at hk
    rw [P.even_length] at hk
    exact qmaInflatedPoint_bounded (P.point e) (P.step e) (hb.2 e) hk
  · intro e
    exact qmaRouteLeaf_bounds (hb.2 e 0 (Nat.zero_le _)).1 (hb.2 e 0 (Nat.zero_le _)).2 _

theorem realize {N : ℚ} (hN : 0 < N) {K X Y d : ℕ} (h3 : 3 ≤ d)
    (hK : ∀ e, P.length e ≤ K) (hb : P.Bounded X Y)
    (hd : ∀ v, qmaGraphDegree G.left G.right v ≤ d) :
    ∃ (H : QMARationalExchangeGraph) (position : Fin H.n → ℕ × ℕ),
      Function.Injective position ∧
      (∀ v, (position v).1 < 8*X ∧ (position v).2 < 8*Y) ∧
      (∀ e, qmaSquareGrid.Adj (position (H.left e)) (position (H.right e))) ∧
      (∀ v, qmaGraphDegree H.left H.right v ≤ d) ∧
      H.n+Fintype.card H.Edge ≤ 5^(4*K+1)*(G.n+Fintype.card G.Edge) ∧
      |H.energy-G.energy| ≤ ((4*K+1:ℕ):ℝ)/(N:ℝ) := by
  have hw : ∀ e, P.toEven.work e ≤ 4*K := by
    intro e
    change 4*P.length e-1 ≤ 4*K
    have h := hK e
    omega
  exact P.toEven.realize hN h3 hw (P.toEven_bounded hb) hd

end QMAPlanarRouteData
end
end ContinuumCoulomb

end OAI
