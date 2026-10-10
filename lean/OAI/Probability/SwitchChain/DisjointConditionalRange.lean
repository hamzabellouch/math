import OAI.Probability.SwitchChain.PairEqualityCell

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem projection_fixes_fluctuation_of_affine
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : PairFiber.Outside i j k) (hl : PairFiber.Outside i j l)
    (u A B : StateSpace n d)
    (hA : A ∈ fiberSpace n d {i,j}) (hB : B ∈ fiberSpace n d {i,j})
    (hBsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → B G = 0)
    (hu : u = A + multiply B (observable i k l)) :
    projection i j k l (fluctuation n d {i,j} u) = fluctuation n d {i,j} u := by
  apply (projection_eq_self_iff _ _ _ _ _).mpr
  rw [hu, map_add, (fluctuation_eq_zero_iff _ _).mpr hA, zero_add]
  exact fluctuation_weighted_observable_mem i j k l hij hk hl B hB hBsupport

theorem cell_function_mem_left (e : Fin 4 ↪ Fin n)
    (a : DisjointEncoding.CellIndex e d → ℝ) :
    WithLp.toLp 2 (fun G : GraphState n d => a (DisjointEncoding.cellIndex e G)) ∈
      fiberSpace n d {e 0,e 1} := by
  intro G H h
  change a (DisjointEncoding.cellIndex e G) = a (DisjointEncoding.cellIndex e H)
  congr 1
  exact (DisjointEncoding.cellIndex_eq_iff e G H).mpr
    (DisjointEncoding.sameCell_of_sameFiber_left e G.val H.val h)

theorem cell_function_mem_right (e : Fin 4 ↪ Fin n)
    (a : DisjointEncoding.CellIndex e d → ℝ) :
    WithLp.toLp 2 (fun G : GraphState n d => a (DisjointEncoding.cellIndex e G)) ∈
      fiberSpace n d {e 2,e 3} := by
  intro G H h
  change a (DisjointEncoding.cellIndex e G) = a (DisjointEncoding.cellIndex e H)
  congr 1
  exact (DisjointEncoding.cellIndex_eq_iff e G H).mpr
    (DisjointEncoding.sameCell_of_sameFiber_right e G.val H.val h)

theorem projection_fixes_fluctuation_of_cell_affine_left (e : Fin 4 ↪ Fin n)
    (u : StateSpace n d) (a b : DisjointEncoding.CellIndex e d → ℝ)
    (hb : ∀ G : GraphState n d, crossTotal (e 0) (e 1) (e 2) (e 3) G ≠ 2 →
      b (DisjointEncoding.cellIndex e G) = 0)
    (hu : ∀ G : GraphState n d,
      u G = a (DisjointEncoding.cellIndex e G) +
        b (DisjointEncoding.cellIndex e G) * observable (e 0) (e 2) (e 3) G) :
    projection (e 0) (e 1) (e 2) (e 3) (fluctuation n d {e 0,e 1} u) =
      fluctuation n d {e 0,e 1} u := by
  have he (i j : Fin 4) (hij : i ≠ j) : e i ≠ e j := fun h => hij (e.injective h)
  apply projection_fixes_fluctuation_of_affine _ _ _ _ (he 0 1 (by decide))
    ⟨he 2 0 (by decide), he 2 1 (by decide)⟩
    ⟨he 3 0 (by decide), he 3 1 (by decide)⟩ u
    (WithLp.toLp 2 (fun G => a (DisjointEncoding.cellIndex e G)))
    (WithLp.toLp 2 (fun G => b (DisjointEncoding.cellIndex e G)))
    (cell_function_mem_left e a) (cell_function_mem_left e b) hb
  ext G
  exact hu G

theorem projection_fixes_fluctuation_of_cell_affine_right (e : Fin 4 ↪ Fin n)
    (u : StateSpace n d) (a b : DisjointEncoding.CellIndex e d → ℝ)
    (hb : ∀ G : GraphState n d, crossTotal (e 2) (e 3) (e 0) (e 1) G ≠ 2 →
      b (DisjointEncoding.cellIndex e G) = 0)
    (hu : ∀ G : GraphState n d,
      u G = a (DisjointEncoding.cellIndex e G) +
        b (DisjointEncoding.cellIndex e G) * observable (e 2) (e 0) (e 1) G) :
    projection (e 2) (e 3) (e 0) (e 1) (fluctuation n d {e 2,e 3} u) =
      fluctuation n d {e 2,e 3} u := by
  have he (i j : Fin 4) (hij : i ≠ j) : e i ≠ e j := fun h => hij (e.injective h)
  apply projection_fixes_fluctuation_of_affine _ _ _ _ (he 2 3 (by decide))
    ⟨he 0 2 (by decide), he 0 3 (by decide)⟩
    ⟨he 1 2 (by decide), he 1 3 (by decide)⟩ u
    (WithLp.toLp 2 (fun G => a (DisjointEncoding.cellIndex e G)))
    (WithLp.toLp 2 (fun G => b (DisjointEncoding.cellIndex e G)))
    (cell_function_mem_right e a) (cell_function_mem_right e b) hb
  ext G
  exact hu G

end Problem315.PairEquality

end

end OAI
