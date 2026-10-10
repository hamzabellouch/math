import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootEuclideanCoordinates

namespace OAI

/-! # Gaussian word coordinates are the actual upper matrix entries -/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma word_column_of_pivot (c : EliminationChain P D) (t : c.Time)
    (i : Fin n) (hi : i ∈ D) (r : Fin n) :
    (c.word t).val r i = if r = i then 1 else 0 := by
  induction c with
  | done => simp [word,Matrix.one_apply]
  | @step P D a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      have hib : i ≠ b := by intro h; exact hb (h ▸ hi)
      change ((tail.word t.1).val * Matrix.transvection a b t.2) r i = _
      rw [Matrix.mul_transvection_apply_of_ne (i := a) (j := b) r i hib]
      exact ih t.1 (Finset.mem_insert_of_mem hi)

lemma word_step_add_single {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r,b) ∈ P → (r,a) ∈ P) (hb : b ∉ D)
    (tail : EliminationChain (insert (a,b) P) (insert a D)) (t : tail.Time) (s : ℝ) :
    ((EliminationChain.step a b hab hP hb tail).word (t,s)).val =
      (tail.word t).val + Matrix.single a b s := by
  ext r i
  change ((tail.word t).val * Matrix.transvection a b s) r i = _
  by_cases hi : i = b
  · subst i
    rw [Matrix.mul_transvection_apply_same,Matrix.add_apply,
      tail.word_column_of_pivot t a (Finset.mem_insert_self _ _) r]
    by_cases hr : r = a
    · subst r; simp
    · simp [hr,Ne.symm hr]
  · rw [Matrix.mul_transvection_apply_of_ne (i := a) (j := b) r i hi,Matrix.add_apply]
    simp [Ne.symm hi]

theorem word_val_eq_sum_single (c : EliminationChain P D) (t : c.Time) :
    (c.word t).val = 1 + ∑ k : Fin c.roots.length,
      Matrix.single (c.roots.get k).1 (c.roots.get k).2 (c.timeVectorHomeomorph t k) := by
  induction c with
  | done =>
      change (1 : Matrix (Fin n) (Fin n) ℝ) = 1 + ∑ k : Fin 0, _
      simp
  | @step P D a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      calc
        _ = (tail.word t.1).val + Matrix.single a b t.2 := word_step_add_single hab hP hb tail _ _
        _ = _ := ?_
      rw [ih]
      change 1 + (∑ k : Fin tail.roots.length, Matrix.single (tail.roots.get k).1
        (tail.roots.get k).2 (tail.timeVectorHomeomorph t.1 k)) + Matrix.single a b t.2 =
        1 + ∑ k : Fin (tail.roots.length+1), Matrix.single (((a,b)::tail.roots).get k).1
          (((a,b)::tail.roots).get k).2
          (Fin.cons t.2 (tail.timeVectorHomeomorph t.1) k)
      rw [Fin.sum_univ_succ]
      simp only [List.get_eq_getElem,Fin.val_zero,List.getElem_cons_zero,Fin.cons_zero,
        Fin.val_succ,List.getElem_cons_succ,Fin.cons_succ]
      abel

end EliminationChain
end DukePrimeDegree

end

end OAI
