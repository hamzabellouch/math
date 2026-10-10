import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutedSubdivision

namespace OAI

/-! Even route lengths use one singlet leaf. The leaf sits beside the first
interior route point and outside all routed edges. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

structure QMAEvenRouteData (G : QMARationalExchangeGraph) where
  work : G.Edge → ℕ
  position : Fin G.n → ℕ × ℕ
  position_injective : Function.Injective position
  point : G.Edge → ℕ → ℕ × ℕ
  first : ∀ e, point e 0 = position (G.left e)
  last : ∀ e, point e (2*work e+2) = position (G.right e)
  simple : ∀ e i j, i ≤ 2*work e+2 → j ≤ 2*work e+2 → point e i = point e j → i = j
  step : ∀ e i, i < 2*work e+2 → qmaSquareGrid.Adj (point e i) (point e (i+1))
  avoids : ∀ e i v, 0 < i → i < 2*work e+2 → point e i ≠ position v
  disjoint : ∀ e f i j, e ≠ f → 0 < i → i < 2*work e+2 → j ≤ 2*work f+2 →
    point e i ≠ point f j
  leaf : G.Edge → ℕ × ℕ
  leaf_injective : Function.Injective leaf
  leaf_step : ∀ e, qmaSquareGrid.Adj (point e 1) (leaf e)
  leaf_avoids : ∀ e f k, k ≤ 2*work f+2 → leaf e ≠ point f k
  leaf_old : ∀ e v, leaf e ≠ position v

namespace QMAEvenRouteData
variable {G : QMARationalExchangeGraph} (P : QMAEvenRouteData G)

def selected (i : Fin (Finset.univ : Finset G.Edge).card) : G.Edge :=
  qmaSelectedIndex Finset.univ i

theorem selected_injective : Function.Injective (selected (G := G)) := by
  intro i j h
  apply (Finset.univ : Finset G.Edge).equivFin.symm.injective
  exact Subtype.ext h

def freshPosition (i : Fin (Finset.univ : Finset G.Edge).card) (b : Fin 2) : ℕ × ℕ :=
  if b = 0 then P.point (selected i) 1 else P.leaf (selected i)

theorem freshPosition_ne_old (i : Fin (Finset.univ : Finset G.Edge).card) (b : Fin 2)
    (v : Fin G.n) : P.freshPosition i b ≠ P.position v := by
  fin_cases b
  · exact P.avoids _ 1 v (by omega) (by omega)
  · exact P.leaf_old _ v

theorem freshPosition_injective : Function.Injective
    (fun x : Fin (Finset.univ : Finset G.Edge).card × Fin 2 => P.freshPosition x.1 x.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change P.freshPosition i a = P.freshPosition j b at h
  fin_cases a <;> fin_cases b
  · have he : selected i = selected j := by
      by_contra hn
      exact P.disjoint _ _ 1 1 hn (by omega) (by omega) (by omega) h
    have hij := selected_injective he
    subst j
    rfl
  · exact (P.leaf_avoids (selected j) (selected i) 1 (by omega) h.symm).elim
  · exact (P.leaf_avoids (selected i) (selected j) 1 (by omega) h).elim
  · have he := P.leaf_injective h
    have hij := selected_injective he
    subst j
    rfl

def nextPosition (v : Fin (G.n+(Finset.univ : Finset G.Edge).card*2)) : ℕ × ℕ :=
  Sum.elim P.position (fun p => P.freshPosition p.1 p.2) ((vertexEquiv _ _).symm v)

@[simp] theorem nextPosition_old (v : Fin G.n) : P.nextPosition (old _ _ v) = P.position v := by
  simp only [nextPosition,old,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem nextPosition_fresh (i : Fin (Finset.univ : Finset G.Edge).card) (b : Fin 2) :
    P.nextPosition (fresh _ _ i b) = P.freshPosition i b := by
  simp only [nextPosition,fresh,Equiv.symm_apply_apply,Sum.elim_inr]

theorem nextPosition_injective : Function.Injective P.nextPosition := by
  intro x y h
  obtain ⟨x,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective x
  obtain ⟨y,rfl⟩ := (vertexEquiv G.n (Finset.univ : Finset G.Edge).card).surjective y
  simp only [nextPosition,Equiv.symm_apply_apply] at h
  apply (vertexEquiv _ _).congr_arg
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (P.position_injective h)
    | inr y => exact (P.freshPosition_ne_old y.1 y.2 x h.symm).elim
  | inr x =>
    cases y with
    | inl y => exact (P.freshPosition_ne_old x.1 x.2 y h).elim
    | inr y => exact congrArg Sum.inr (P.freshPosition_injective h)

def nextWork : QMAPartialPathsEdge (Finset.univ : Finset G.Edge) → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr (i,a)) => if a = 1 then P.work (selected i) else 0

def schedule (N : ℚ) : QMAPathSchedule where
  graph := G.subdivide Finset.univ (fun _ => true) N
  work := P.nextWork

theorem schedule_work_le (N : ℚ) {D : ℕ} (hD : ∀ e, P.work e ≤ D) :
    ∀ e, (P.schedule N).work e ≤ D := by
  intro e
  rcases e with e | (i | ⟨i,a⟩)
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · change (if a = 1 then P.work (selected i) else 0) ≤ D
    split
    · exact hD _
    · exact Nat.zero_le _

theorem schedule_energy_error {N : ℚ} (hN : 0 < N) :
    |(P.schedule N).graph.energy-G.energy| ≤ 1/(N:ℝ) :=
  G.subdivide_energy_error Finset.univ (fun _ => true) hN

end QMAEvenRouteData
end ContinuumCoulomb

end

end OAI
