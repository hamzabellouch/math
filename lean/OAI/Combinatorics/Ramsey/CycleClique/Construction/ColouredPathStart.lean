import OAI.Combinatorics.Ramsey.CycleClique.Construction.ColouredPath
import OAI.Combinatorics.Ramsey.CycleClique.Construction.DeletedComponent

namespace OAI

/-! Initial longest-path obstruction in the coloured-path proof. -/

namespace CycleClique.Construction
theorem indexedPath_prefix {V : Type*} {G : SimpleGraph V} {q r : ℕ}
    {f : Fin (q + 1) → V} (hf : IsIndexedPath G f) (hrq : r ≤ q) :
    IsIndexedPath G (fun i : Fin (r + 1) => f (Fin.castLE (by omega) i)) := by
  refine ⟨hf.1.comp (Fin.castLE_injective _), ?_⟩
  intro i
  exact hf.2 ⟨i.val, by have := i.isLt; omega⟩

theorem indexedPath_cons {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f) {v : V}
    (hv : v ∉ Set.range f) (hadj : G.Adj v (f 0)) :
    IsIndexedPath G (Fin.cons v f) := by
  refine ⟨Fin.cons_injective_iff.mpr ⟨hv, hf.1⟩, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hadj
  · have heq : j.succ.castSucc = j.castSucc.succ := Fin.ext rfl
    rw [heq]
    simpa only [Fin.cons_succ] using hf.2 j

/-- One of two differently coloured common neighbours can prefix any
path avoiding them, producing different colours at its two ends. -/
theorem colored_path_of_common_neighbor {V : Type*} {H : SimpleGraph V}
    {x y z : V} (hxy : H.Adj x y) (hxz : H.Adj x z)
    (χ : V → Fin 2) (hyz : χ y ≠ χ z) {q : ℕ}
    {f : Fin (q + 1) → V} (hf : IsIndexedPath H f) (hstart : f 0 = x)
    (havoid : ∀ i, f i ≠ y ∧ f i ≠ z) :
    ∃ g : Fin (q + 1 + 1) → V, IsIndexedPath H g ∧
      χ (g 0) ≠ χ (g (Fin.last (q + 1))) := by
  have hyavoid : y ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact (havoid i).1 hi
  have hzavoid : z ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact (havoid i).2 hi
  by_cases hycol : χ y = χ (f (Fin.last q))
  · refine ⟨Fin.cons z f, indexedPath_cons hf hzavoid (by rw [hstart]; exact hxz.symm), ?_⟩
    simp only [Fin.cons_zero, Fin.cons_last]
    intro hzcol
    exact hyz (hycol.trans hzcol.symm)
  · refine ⟨Fin.cons y f, indexedPath_cons hf hyavoid (by rw [hstart]; exact hxy.symm), ?_⟩
    simpa only [Fin.cons_zero, Fin.cons_last] using hycol

/-- Under failure of the desired exact-length coloured path, every
path starting at the common neighbour in the deletion has smaller order. -/
theorem no_colored_path_start_bound {V : Type*} {H : SimpleGraph V}
    {x y z : V} (hxy : H.Adj x y) (hxz : H.Adj x z)
    (χ : V → Fin 2) (hyz : χ y ≠ χ z) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hno : ¬ ∃ g : Fin (ℓ + 1) → V, IsIndexedPath H g ∧
      χ (g 0) ≠ χ (g (Fin.last ℓ)))
    {q : ℕ} {f : Fin (q + 1) → V} (hf : IsIndexedPath H f) (hstart : f 0 = x)
    (havoid : ∀ i, f i ≠ y ∧ f i ≠ z) : q + 1 < ℓ := by
  cases ℓ with
  | zero => omega
  | succ ℓ =>
    by_contra hn
    have hbound : ℓ ≤ q := by omega
    let f' : Fin (ℓ + 1) → V := fun i => f (Fin.castLE (by omega) i)
    have hf' : IsIndexedPath H f' := indexedPath_prefix hf hbound
    have hstart' : f' 0 = x := hstart
    have havoid' : ∀ i, f' i ≠ y ∧ f' i ≠ z := fun i => havoid _
    obtain ⟨g, hg, hcolor⟩ := colored_path_of_common_neighbor hxy hxz χ hyz hf' hstart' havoid'
    exact hno ⟨g, hg, hcolor⟩

end CycleClique.Construction

end OAI
