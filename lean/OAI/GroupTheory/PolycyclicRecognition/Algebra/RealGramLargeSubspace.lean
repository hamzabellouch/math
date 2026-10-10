import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealGramSimultaneousDiagonal
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicSpectralSubspace

namespace OAI

/-! # A large subspace with controlled quadratic-form growth -/
noncomputable section
namespace PolycyclicRecognition
open Matrix Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realMatrixQuadratic (A : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (A *ᵥ v)

omit [DecidableEq ι] in
theorem realMatrixQuadratic_congruence (A T : Matrix ι ι ℝ) (v : ι → ℝ) :
    realMatrixQuadratic A (T *ᵥ v) = realMatrixQuadratic (Tᴴ * A * T) v := by
  simp only [realMatrixQuadratic, conjTranspose_eq_transpose_of_trivial,
    ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem realMatrixQuadratic_one (v : ι → ℝ) :
    realMatrixQuadratic (1 : Matrix ι ι ℝ) v = ∑ i, (v i) ^ 2 := by
  simp [realMatrixQuadratic, dotProduct, pow_two]

theorem realMatrixQuadratic_diagonal (ev v : ι → ℝ) :
    realMatrixQuadratic (diagonal ev) v = ∑ i, ev i * (v i) ^ 2 := by
  simp only [realMatrixQuadratic, dotProduct]
  apply sum_congr rfl
  intro i _
  simp only [mulVec_diagonal]
  ring

theorem real_ordered_forms_large_subspace {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hAB : (B - A).PosSemidef)
    (K : ℝ) (hK : 1 < K) (hdet : B.det ≤ K ^ Fintype.card ι * A.det) :
    ∃ W : Submodule ℝ (ι → ℝ), Fintype.card ι ≤ 2 * Module.finrank ℝ W ∧
      ∀ v ∈ W, realMatrixQuadratic B v ≤ K ^ 2 * realMatrixQuadratic A v := by
  obtain ⟨T, ev, hT, hTA, hTB, hev⟩ := real_ordered_forms_simultaneous_diagonal hA hAB
  have hp := real_ordered_forms_diagonal_product_bound ev hTA hTB K hdet
  have hi : Function.Injective T.mulVecLin := Matrix.mulVec_injective_iff_isUnit.mpr hT
  let W := (spectralSmallSubspace ev K).map T.mulVecLin
  have hd : Module.finrank ℝ W = Module.finrank ℝ (spectralSmallSubspace ev K) :=
    (Submodule.equivMapOfInjective T.mulVecLin hi (spectralSmallSubspace ev K)).finrank_eq.symm
  refine ⟨W, by rw [hd]; exact spectralSmallSubspace_dimension ev K hK hev hp, ?_⟩
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
  change realMatrixQuadratic B (T *ᵥ x) ≤ K ^ 2 * realMatrixQuadratic A (T *ᵥ x)
  rw [realMatrixQuadratic_congruence, realMatrixQuadratic_congruence, hTA, hTB,
    realMatrixQuadratic_one, realMatrixQuadratic_diagonal]
  exact spectralSmallSubspace_quadratic_bound ev K ⟨x, hx⟩

end PolycyclicRecognition

end

end OAI
