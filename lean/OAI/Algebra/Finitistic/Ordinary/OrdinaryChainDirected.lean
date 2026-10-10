import OAI.Algebra.Finitistic.Ordinary.OrdinaryChainAlgebra
import OAI.Algebra.Finitistic.Encoding.DirectedBound

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

theorem vertex_orthogonal (i j : Fin (l+1)) (hij : i ≠ j) : vertex k l i * vertex k l j = 0 := by
  apply Prod.ext
  · funext t
    change (Pi.single i (1:k) : Fin (l+1) → k) t * (Pi.single j (1:k) : Fin (l+1) → k) t = 0
    by_cases ht : t=i
    · subst t; simp [hij.symm]
    · simp [ht]
  · funext t
    change (Pi.single i (1:k) : Fin (l+1) → k) t.succ * 0 + 0 * (Pi.single j (1:k) : Fin (l+1) → k) t.castSucc = 0
    simp

theorem vertex_complete : ∑ i : Fin (l+1), vertex k l i = 1 := by
  apply Prod.ext
  · funext t
    have h := map_sum ((LinearMap.proj t).comp
      (LinearMap.fst k (Fin (l+1) → k) (Fin l → k))) (fun i : Fin (l+1) => vertex k l i) Finset.univ
    change (∑ i : Fin (l+1), vertex k l i).1 t = 1
    exact h.trans (by
      change (∑ i : Fin (l+1), (Pi.single i (1:k) : Fin (l+1) → k) t) = 1
      simp [Pi.single_apply])
  · funext t
    have h := map_sum ((LinearMap.proj t).comp
      (LinearMap.snd k (Fin (l+1) → k) (Fin l → k))) (fun i : Fin (l+1) => vertex k l i) Finset.univ
    change (∑ i : Fin (l+1), vertex k l i).2 t = 0
    exact h.trans (by
      change (∑ _i : Fin (l+1), (0:k)) = 0
      simp)

theorem vertex_corner_diagonal (i : Fin (l+1)) (x : ChainAlgebra k l) :
    vertex k l i * x * vertex k l i = x.1 i • vertex k l i := by
  apply Prod.ext
  · funext t
    change ((Pi.single i (1:k) : Fin (l+1) → k) t * x.1 t) *
      (Pi.single i (1:k) : Fin (l+1) → k) t = x.1 i * (Pi.single i (1:k) : Fin (l+1) → k) t
    by_cases ht : t=i <;> simp [ht]
  · funext t
    change ((Pi.single i (1:k) : Fin (l+1) → k) t.succ * x.1 t.succ) * 0 +
      ((Pi.single i (1:k) : Fin (l+1) → k) t.succ * x.2 t + 0 * x.1 t.castSucc) *
        (Pi.single i (1:k) : Fin (l+1) → k) t.castSucc = x.1 i * 0
    by_cases h₁ : t.succ = i
    · have h₂ : t.castSucc ≠ i := by intro h; have := congrArg Fin.val h₁; have := congrArg Fin.val h; simp at *; omega
      simp [h₂]
    · simp [h₁]

theorem vertex_directed (i j : Fin (l+1)) (hij : j < i) (x : ChainAlgebra k l) :
    vertex k l j * x * vertex k l i = 0 := by
  apply Prod.ext
  · funext t
    change ((Pi.single j (1:k) : Fin (l+1) → k) t * x.1 t) *
      (Pi.single i (1:k) : Fin (l+1) → k) t = 0
    by_cases ht : t=j
    · subst t; simp [ne_of_lt hij]
    · simp [ht]
  · funext t
    change ((Pi.single j (1:k) : Fin (l+1) → k) t.succ * x.1 t.succ) * 0 +
      ((Pi.single j (1:k) : Fin (l+1) → k) t.succ * x.2 t + 0 * x.1 t.castSucc) *
        (Pi.single i (1:k) : Fin (l+1) → k) t.castSucc = 0
    by_cases h₁ : t.succ=j
    · have h₂ : t.castSucc ≠ i := by
        intro h
        have := congrArg Fin.val h₁
        have := congrArg Fin.val h
        change j.val < i.val at hij
        simp at *
        omega
      simp [h₂]
    · simp [h₁]

/-- The actual chain algebra has the source's directed vertex system, including l=0. -/
def directedSystem : DirectedBound.DirectedSystem k (ChainAlgebra k l) (l+1) where
  e := vertex k l
  idem := vertex_idempotent k l
  orthogonal := vertex_orthogonal k l
  complete := vertex_complete k l
  diagonal i x := ⟨x.1 i,vertex_corner_diagonal k l i x⟩
  directed := vertex_directed k l
end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
