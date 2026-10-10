import OAI.Algebra.DepthFive.UpperBlockData
import OAI.Algebra.DepthFive.MatrixPathSemantics

namespace OAI

noncomputable section

namespace Problem335.BlockData

variable {n : ℕ}

/-- The lower-gate monomial belonging to an enumerated block path. -/
def lowerMonomial (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (p : Lower blocks) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((lowerInputs blocks p).map MvPolynomial.X).prod

/-- The weighted middle input list computes exactly the corresponding block matrix entry. -/
theorem middleInputs_value (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (m : Middle blocks) :
    ((middleInputs K blocks m).map (fun e =>
      MvPolynomial.C e.1 * lowerMonomial K blocks e.2)).sum =
      (((blocks.get m.1).map (immLayer K n)).prod) m.2.1 m.2.2 := by
  simp only [middleInputs, List.map_ofFn, Function.comp_def, lowerMonomial,
    lowerInputs, MvPolynomial.C_1, one_mul, List.sum_ofFn]
  exact matrixEntryPaths_fin_sum_prod (immLayer K n) (blocks.get m.1) m.2.1 m.2.2

/-- Substitute lower-gate semantics into the middle gate. -/
theorem middleInputs_value_of_lower
    (K : Type*) [CommSemiring K] (blocks : List (List (Fin n)))
    (v : Lower blocks → MvPolynomial (Fin n × Fin n × Fin n) K)
    (hv : ∀ p, v p = lowerMonomial K blocks p) (m : Middle blocks) :
    ((middleInputs K blocks m).map (fun e => MvPolynomial.C e.1 * v e.2)).sum =
      (((blocks.get m.1).map (immLayer K n)).prod) m.2.1 m.2.2 := by
  simp_rw [hv]
  exact middleInputs_value K blocks m

end Problem335.BlockData

end

end OAI
