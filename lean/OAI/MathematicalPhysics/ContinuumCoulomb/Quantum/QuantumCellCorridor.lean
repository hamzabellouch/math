import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellTranslate

namespace OAI

/-! The actual short lattice corridor between neighboring cells, with either
ordinary or inward-moved terminals at each end. -/

namespace ContinuumCoulomb

def qmaPortOpposite : Fin 4 → Fin 4 := ![2,3,0,1]

theorem qmaCellBoundary_step (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4) :
    qmaSquareGrid.Adj (qmaCellTranslate p (qmaCellBoundary a))
      (qmaCellTranslate (qmaGridNeighbor p a) (qmaCellBoundary (qmaPortOpposite a))) := by
  fin_cases a <;>
    dsimp [qmaCellTranslate,qmaCellBoundary,qmaPortOpposite,qmaGridNeighbor]
  all_goals change Nat.dist _ _ + Nat.dist _ _ = 1
  all_goals unfold Nat.dist; omega

def qmaHalfPathAt (p : ℕ × ℕ) (cross : Bool) (a : Fin 4) : List (ℕ × ℕ) :=
  (qmaHalfCorridorPath cross a).map (qmaCellTranslate p)

theorem qmaHalfPathAt_endpoints (p : ℕ × ℕ) (cross : Bool) (a : Fin 4) :
    (qmaHalfPathAt p cross a).head? = some (qmaCellTranslate p (qmaLocalPort cross a)) ∧
    (qmaHalfPathAt p cross a).getLast? = some (qmaCellTranslate p (qmaCellBoundary a)) := by
  simp only [qmaHalfPathAt,List.head?_map,List.getLast?_map,
    (qmaHalfCorridor_endpoints cross a).1,(qmaHalfCorridor_endpoints cross a).2,Option.map_some]
  constructor <;> trivial

theorem qmaHalfPathAt_chain (p : ℕ × ℕ) (cross : Bool) (a : Fin 4) :
    (qmaHalfPathAt p cross a).IsChain (fun x y => qmaSquareGrid.Adj x y) := by
  apply List.isChain_map_of_isChain (qmaCellTranslate p) _ (qmaHalfCorridor_chain cross a)
  intro x y h
  change Nat.dist _ _ + Nat.dist _ _ = 1
  simpa only [qmaCellTranslate_step] using h

theorem qmaHalfPathAt_simple (p : ℕ × ℕ) (cross : Bool) (a : Fin 4) :
    (qmaHalfPathAt p cross a).Nodup :=
  (qmaHalfCorridor_simple cross a).map (qmaCellTranslate_injective p)

theorem qmaHalfPathAt_mem {p z : ℕ × ℕ} {cross : Bool} {a : Fin 4}
    (hz : z ∈ qmaHalfPathAt p cross a) :
    ∃ u, u.1 < 32 ∧ u.2 < 32 ∧ qmaCellTranslate p u = z := by
  obtain ⟨u,hu,he⟩ := List.mem_map.mp hz
  exact ⟨u,(qmaHalfCorridor_bounded cross a u hu).1,
    (qmaHalfCorridor_bounded cross a u hu).2,he⟩

def qmaCellCorridor (p : ℕ × ℕ) (a : Fin 4) (cross nextCross : Bool) : List (ℕ × ℕ) :=
  qmaHalfPathAt p cross a ++
    (qmaHalfPathAt (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)).reverse

theorem qmaCellCorridor_endpoints (p : ℕ × ℕ) (a : Fin 4) (cross nextCross : Bool) :
    (qmaCellCorridor p a cross nextCross).head? =
      some (qmaCellTranslate p (qmaLocalPort cross a)) ∧
    (qmaCellCorridor p a cross nextCross).getLast? =
      some (qmaCellTranslate (qmaGridNeighbor p a) (qmaLocalPort nextCross (qmaPortOpposite a))) := by
  simp only [qmaCellCorridor,List.head?_append,List.getLast?_append,List.head?_reverse,List.getLast?_reverse,
    (qmaHalfPathAt_endpoints p cross a).1,
    (qmaHalfPathAt_endpoints (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)).1,Option.some_or]
  constructor <;> trivial

theorem qmaCellCorridor_chain (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4)
    (cross nextCross : Bool) :
    (qmaCellCorridor p a cross nextCross).IsChain (fun x y => qmaSquareGrid.Adj x y) := by
  apply (qmaHalfPathAt_chain p cross a).append
  · apply List.isChain_reverse.mpr
    exact (qmaHalfPathAt_chain (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)).imp
      (fun _ _ h => h.symm)
  · intro x hx y hy
    rw [(qmaHalfPathAt_endpoints p cross a).2] at hx
    rw [List.head?_reverse,
      (qmaHalfPathAt_endpoints (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)).2] at hy
    have hx' := Option.mem_def.mp hx
    have hy' := Option.mem_def.mp hy
    cases hx'
    cases hy'
    exact qmaCellBoundary_step p hp a

theorem qmaCellCorridor_simple (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4)
    (cross nextCross : Bool) : (qmaCellCorridor p a cross nextCross).Nodup := by
  apply (qmaHalfPathAt_simple p cross a).append
    (List.nodup_reverse.mpr (qmaHalfPathAt_simple (qmaGridNeighbor p a) nextCross (qmaPortOpposite a)))
  apply List.disjoint_left.mpr
  intro z hz hy
  obtain ⟨u,hu,hv,he⟩ := qmaHalfPathAt_mem hz
  obtain ⟨v,hv1,hv2,hf⟩ := qmaHalfPathAt_mem (List.mem_reverse.mp hy)
  have hh := qmaCellTranslate_unique ⟨hu,hv⟩ ⟨hv1,hv2⟩ (he.trans hf.symm)
  exact (qmaGridNeighbor_adj p hp.1 hp.2 a).ne hh.1

theorem qmaCellCorridor_length (p : ℕ × ℕ) (a : Fin 4) (cross nextCross : Bool) :
    18 ≤ (qmaCellCorridor p a cross nextCross).length ∧
      (qmaCellCorridor p a cross nextCross).length ≤ 21 := by
  simp only [qmaCellCorridor,qmaHalfPathAt,List.length_append,List.length_reverse,List.length_map]
  cases cross <;> cases nextCross <;> fin_cases a <;> decide

end ContinuumCoulomb

end OAI
