import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductDiagonal

namespace OAI

/-! # Exact shift of future atoms along remaining-root leaves -/

noncomputable section
open Set
open MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingFutureAtom (c : EliminationChain P D) (ell : Fin n → ℝ)
    (hell : ∑ k, ell k = 0) (Q : X n → ℕ) (m : ℕ) (x : X n) : Set c.Time :=
  {u | ∀ k : ℕ,
    Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m]
      (rightAction x (c.word u))) =
    Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] x)}

lemma measurableSet_remainingFutureAtom (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) (x : X n) :
    MeasurableSet (c.remainingFutureAtom ell hell Q m x) := by
  let T : X n → X n := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  change MeasurableSet {u | ∀ k : ℕ, Q (T^[k+m] (rightAction x (c.word u))) = _}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (hQ.comp ((hT.iterate (k+m)).comp hF)) (measurableSet_singleton _)

lemma remainingFutureAtom_zero_subset_one (c : EliminationChain P D)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ) (x : X n) :
    c.remainingFutureAtom ell hell Q 0 x ⊆ c.remainingFutureAtom ell hell Q 1 x := by
  intro u hu k
  simpa only [Nat.add_zero] using hu (k+1)

lemma remaining_orbit_diagonal (c : EliminationChain P D)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (x : X n) (u : c.Time) :
    rightAction (rightAction x (diagonalOneParameter ell hell (-1)))
        (c.word (c.rootDilation ell 1 u)) =
      rightAction (rightAction x (c.word u)) (diagonalOneParameter ell hell (-1)) := by
  rw [rightAction_mul, rightAction_mul, c.word_rootDilation ell hell 1,
    diagonalOneParameter_neg]
  congr 1
  group

theorem remainingFutureAtom_shift (c : EliminationChain P D)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ) (x : X n) :
    (c.rootDilation ell 1) ⁻¹'
      c.remainingFutureAtom ell hell Q 0
        (rightAction x (diagonalOneParameter ell hell (-1))) =
      c.remainingFutureAtom ell hell Q 1 x := by
  ext u
  simp only [mem_preimage, remainingFutureAtom, Set.mem_ofPred_eq, Nat.add_zero,
    c.remaining_orbit_diagonal ell hell, Function.iterate_succ_apply]

end EliminationChain
end DukePrimeDegree

end

end OAI
