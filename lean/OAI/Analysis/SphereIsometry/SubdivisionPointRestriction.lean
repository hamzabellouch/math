import OAI.Analysis.SphereIsometry.SubdivisionRestriction
import OAI.Analysis.SphereIsometry.IteratedPoints

namespace OAI

/-! # Coordinate compatibility of original-face restriction -/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem iterDataPoint_embedding_apply (e : I ↪ J) :
    ∀ (k : ℕ) (v : (iterData I k).Vertex) (i : I),
      iterDataPoint J k ((iterEmbedding e k).toEmbedding v) (e i) =
        iterDataPoint I k v i := by
  intro k
  induction k with
  | zero =>
      intro v i
      change (Pi.single (e v) 1 : J → ℝ) (e i) = (Pi.single v 1 : I → ℝ) i
      by_cases h : i = v
      · subst i
        exact (Pi.single_eq_same (M := fun _ : J => ℝ) (e v) 1).trans
          (Pi.single_eq_same (M := fun _ : I => ℝ) v 1).symm
      · have he : e i ≠ e v := fun he => h (e.injective he)
        exact (Pi.single_eq_of_ne (M := fun _ : J => ℝ) he 1).trans
          (Pi.single_eq_of_ne (M := fun _ : I => ℝ) h 1).symm
  | succ k ih =>
      intro v i
      change finiteBarycenter (iterDataPoint J k)
          (v.val.map (iterEmbedding e k).toEmbedding) (e i) =
        finiteBarycenter (iterDataPoint I k) v.val i
      rw [finiteBarycenter_apply, finiteBarycenter_apply, Finset.card_map]
      congr 1
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl (fun w _ => ih w i)

theorem iterDataPoint_embedding_eq_zero (e : I ↪ J) (k : ℕ)
    (v : (iterData I k).Vertex) {j : J} (hj : j ∉ Set.range e) :
    iterDataPoint J k ((iterEmbedding e k).toEmbedding v) j = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hpos
    have hmem : j ∈ positiveCarrier
        (iterDataPoint J k ((iterEmbedding e k).toEmbedding v)) :=
      mem_positiveCarrier.mpr hpos
    rw [positiveCarrier_iterDataPoint, iterEmbedding_carrier] at hmem
    obtain ⟨i, _, hij⟩ := Finset.mem_map.mp hmem
    exact hj ⟨i, hij⟩
  · exact (iterDataPoint_mem_stdSimplex J k ((iterEmbedding e k).toEmbedding v)).1 j

theorem lastFace_point_castSucc (m k : ℕ) (v : IterVertex m k) (i : Fin (m + 1)) :
    iterPoint (m + 1) k (lastFaceEmbedding m k v) i.castSucc = iterPoint m k v i :=
  iterDataPoint_embedding_apply Fin.castSuccEmb k v i

theorem lastFace_point_last (m k : ℕ) (v : IterVertex m k) :
    iterPoint (m + 1) k (lastFaceEmbedding m k v) (Fin.last (m + 1)) = 0 := by
  apply iterDataPoint_embedding_eq_zero Fin.castSuccEmb k v
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

end Tingley

end

end OAI
