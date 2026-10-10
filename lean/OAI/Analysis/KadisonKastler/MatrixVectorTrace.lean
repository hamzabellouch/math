import OAI.Analysis.KadisonKastler.MatrixTrace
import OAI.Analysis.KadisonKastler.HilbertMatrix
import OAI.Analysis.KadisonKastler.ConcreteTraceTransfer

namespace OAI

/-! # Finite vector formulas for the normalized matrix trace -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {B ι H : Type*} [CStarAlgebra B]
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixVectorTraceOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance matrixVectorTraceStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

omit [Nonempty ι] [CompleteSpace H] in
theorem inner_tupleSingle_hilbertMatrix (x : CStarMatrix ι ι (H →L[ℂ] H))
    (i : ι) (ξ η : H) :
    inner ℂ (Generator.tupleSingle i η) (hilbertMatrix x (Generator.tupleSingle i ξ)) =
      inner ℂ η (x i i ξ) := by
  simp [PiLp.inner_apply, Generator.tupleSingle_apply, Pi.single_apply,
    hilbertMatrix_apply, apply_ite]
  rw [Finset.sum_eq_single i] <;> simp_all

/-- A finite vector formula for the base trace gives one for the matrix
trace, by placing each vector in each coordinate of the direct sum. -/
theorem matrixTrace_vector_formula (τ : FaithfulTracialState B)
    (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) {k : ℕ} (ξ η : Fin k → H)
    (hτ : ∀ b, τ.toLinearMap b = ∑ a, inner ℂ (η a) (ρ b (ξ a)))
    (x : CStarMatrix ι ι B) :
    (matrixTrace τ).toLinearMap x =
      ∑ i : ι, ∑ a : Fin k,
        inner ℂ (Generator.tupleSingle i (η a))
          (hilbertMatrix (x.map ρ)
            (((((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ)) • Generator.tupleSingle i (ξ a))) := by
  simp only [map_smul, inner_smul_right, inner_tupleSingle_hilbertMatrix,
    CStarMatrix.map_apply, matrixTrace_apply, hτ, Finset.mul_sum]

theorem matrixTrace_finiteVector_formula (τ : FaithfulTracialState B)
    (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hτ : ∃ (k : ℕ) (ξ η : Fin k → H),
      ∀ b, τ.toLinearMap b = ∑ a, inner ℂ (η a) (ρ b (ξ a))) :
    ∃ (m : ℕ) (ξ η : Fin m → Generator.FiniteHilbert ι H),
      ∀ x : CStarMatrix ι ι B,
        (matrixTrace τ).toLinearMap x = ∑ a, inner ℂ (η a) (hilbertMatrix (x.map ρ) (ξ a)) := by
  obtain ⟨k, ξ, η, hτ⟩ := hτ
  let e := Fintype.equivFin (ι × Fin k)
  let ξ' (a : ι × Fin k) : Generator.FiniteHilbert ι H :=
    (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) • Generator.tupleSingle a.1 (ξ a.2)
  let η' (a : ι × Fin k) : Generator.FiniteHilbert ι H :=
    Generator.tupleSingle a.1 (η a.2)
  refine ⟨Fintype.card (ι × Fin k), ξ' ∘ e.symm, η' ∘ e.symm, ?_⟩
  intro x
  simp only [Function.comp_apply]
  rw [← e.sum_comp (fun a => inner ℂ (η' (e.symm a))
    (hilbertMatrix (x.map ρ) (ξ' (e.symm a))))]
  simp only [e.symm_apply_apply, Fintype.sum_prod_type]
  exact matrixTrace_vector_formula τ ρ ξ η hτ x

end

end KadisonKastler

end OAI
