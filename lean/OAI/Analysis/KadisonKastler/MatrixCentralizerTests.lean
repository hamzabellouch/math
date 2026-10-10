import OAI.Analysis.KadisonKastler.FiniteMatrixInjectivity

namespace OAI

/-! # Matrix-unit tests for a vector-state centralizer -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixUnits_vector_centralizes (E : MatrixUnitSystem ι (Algebra M)) (ξ : H)
    (h : ∀ i j (x : Algebra M),
      inner ℂ ξ ((E.entry i j * x).val ξ) = inner ℂ ξ ((x * E.entry i j).val ξ))
    (a x : Algebra M) (ha : a ∈ E.algebra) :
    inner ℂ ξ ((a * x).val ξ) = inner ℂ ξ ((x * a).val ξ) := by
  obtain ⟨b,rfl⟩ := E.mem_algebra a |>.mp ha
  simp only [Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, AddSubmonoidClass.coe_finsetSum,
    SetLike.val_smul, sum_apply, smul_apply, inner_sum, inner_smul_right,h]

end

end KadisonKastler

end OAI
