import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOddPathGeometry

namespace OAI

/-! Geometric invariants for the variable-length path-subdivision schedule. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped Classical

structure QMAPathEmbedding (W : QMAPathSchedule)
    (Γ : SimpleGraph (ℕ × ℕ) := qmaSquareGrid) where
  position : Fin W.graph.n → ℕ × ℕ
  position_injective : Function.Injective position
  point : W.graph.Edge → ℕ → ℕ × ℕ
  first : ∀ e, point e 0 = position (W.graph.left e)
  last : ∀ e, point e (2*W.work e+1) = position (W.graph.right e)
  simple : ∀ e i j, i ≤ 2*W.work e+1 → j ≤ 2*W.work e+1 → point e i = point e j → i = j
  step : ∀ e i, i < 2*W.work e+1 → Γ.Adj (point e i) (point e (i+1))
  avoids : ∀ e i v, 0 < i → i < 2*W.work e+1 → point e i ≠ position v
  disjoint : ∀ e f i j, e ≠ f → 0 < i → i < 2*W.work e+1 → j ≤ 2*W.work f+1 →
    point e i ≠ point f j

namespace QMAPathEmbedding
variable {W : QMAPathSchedule} {Γ : SimpleGraph (ℕ × ℕ)} (P : QMAPathEmbedding W Γ)

theorem selected_work_pos (i : Fin W.active.card) : 0 < W.work (qmaSelectedIndex W.active i) :=
  (W.mem_active _).mp (qmaSelectedIndex_mem W.active i)

def freshPosition (i : Fin W.active.card) (b : Fin 2) : ℕ × ℕ :=
  P.point (qmaSelectedIndex W.active i) (b.val+1)

theorem freshPosition_ne_old (i : Fin W.active.card) (b : Fin 2) (v : Fin W.graph.n) :
    P.freshPosition i b ≠ P.position v := by
  apply P.avoids
  · omega
  · have h := selected_work_pos (W := W) i
    have hb := b.isLt
    omega

theorem freshPosition_injective : Function.Injective (fun x : Fin W.active.card × Fin 2 =>
    P.freshPosition x.1 x.2) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change P.point (qmaSelectedIndex W.active i) (a.val+1) =
    P.point (qmaSelectedIndex W.active j) (b.val+1) at h
  have hi := selected_work_pos (W := W) i
  have hj := selected_work_pos (W := W) j
  have ha := a.isLt
  have hb := b.isLt
  have he : qmaSelectedIndex W.active i = qmaSelectedIndex W.active j := by
    by_contra hn
    exact P.disjoint _ _ (a.val+1) (b.val+1) hn (by omega) (by omega) (by omega) h
  have hij : i = j := by
    apply W.active.equivFin.symm.injective
    exact Subtype.ext he
  subst j
  have hab := P.simple (qmaSelectedIndex W.active i) (a.val+1) (b.val+1) (by omega) (by omega) h
  have : a = b := Fin.ext (by omega)
  subst b
  rfl

def nextPosition (v : Fin (W.graph.n+W.active.card*2)) : ℕ × ℕ :=
  Sum.elim P.position (fun p => P.freshPosition p.1 p.2) ((vertexEquiv _ _).symm v)

@[simp] theorem nextPosition_old (v : Fin W.graph.n) :
    P.nextPosition (old _ _ v) = P.position v := by simp [nextPosition,old]

@[simp] theorem nextPosition_fresh (e : Fin W.active.card) (b : Fin 2) :
    P.nextPosition (fresh _ _ e b) = P.freshPosition e b := by simp [nextPosition,fresh]

theorem nextPosition_injective : Function.Injective P.nextPosition := by
  intro x y h
  obtain ⟨x,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective x
  obtain ⟨y,rfl⟩ := (vertexEquiv W.graph.n W.active.card).surjective y
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

theorem adjacent_of_complete (h : ∀ e, W.work e = 0) (e : W.graph.Edge) :
    Γ.Adj (P.position (W.graph.left e)) (P.position (W.graph.right e)) := by
  have hs := P.step e 0 (by omega)
  have hl := P.last e
  simp only [h e,Nat.mul_zero,Nat.zero_add] at hl
  simpa only [P.first e,hl] using hs

end QMAPathEmbedding
end ContinuumCoulomb

end

end OAI
