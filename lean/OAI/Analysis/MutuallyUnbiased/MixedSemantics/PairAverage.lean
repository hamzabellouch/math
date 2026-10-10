import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.Certificate.Interpretation

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

/-- The pair certificate coordinates averaged over ordered pairs of bases. -/
def familyPairVector (B : Fin 7 → Basis) : Fin 909 → ℝ :=
  fun i => familyAverage B (fun H => PairSemantics.momentVector H i)

theorem familyPairVector_abs_le_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (i : Fin 909) :
    |familyPairVector B i| ≤ 1 := by
  apply abs_average_le_one
  intro r
  apply abs_average_le_one
  intro s
  exact injectiveMoment_abs_le_one (relativeMatrix_isHadamard B hB r s) _

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

end OAI
