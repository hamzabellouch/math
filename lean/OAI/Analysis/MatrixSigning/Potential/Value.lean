import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Parameters

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def value (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) : ℝ :=
  sInf (objective ε '' feasible S η)

lemma value_eq_of_min (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    value ε S η = objective ε z := by
  apply IsLeast.csInf_eq
  refine ⟨⟨z,hz,rfl⟩,?_⟩
  rintro b ⟨w,hw,rfl⟩
  exact hmin w hw

lemma value_eq_of_kkt (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hηsym : SymmetricMap η) (z : Point d) (hz : z ∈ domain d)
    (P Q : H d) (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d)
    (htr : realTrace P + realTrace Q = 1)
    (hX : sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d))
    (hY : sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d))
    (htight : residual S η z = 0) : value ε S η = objective ε z := by
  obtain ⟨hf,hm⟩ := optimal_of_kkt ε S η hηsym z hz P Q hP hQ htr hX hY htight
  exact value_eq_of_min ε S η z hf hm

end
end CurrentKS.Variational

end OAI
