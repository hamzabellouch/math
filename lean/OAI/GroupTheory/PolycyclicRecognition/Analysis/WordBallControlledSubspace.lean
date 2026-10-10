import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealGramLargeSubspace
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallGramOrder

namespace OAI

/-! # A large controlled-growth subspace of actual functions -/
noncomputable section
namespace PolycyclicRecognition
open Matrix Finset
variable {G : Type*} [Group G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def basisFunctionsLinearMap (V : Submodule ℝ (G → ℝ)) (basis : Module.Basis ι ℝ V) :
    (ι → ℝ) →ₗ[ℝ] (G → ℝ) := V.subtype.comp basis.equivFun.symm.toLinearMap

omit [Group G] [DecidableEq G] [DecidableEq ι] in
theorem basisFunctionsLinearMap_apply (V : Submodule ℝ (G → ℝ))
    (basis : Module.Basis ι ℝ V) (v : ι → ℝ) (x : G) :
    basisFunctionsLinearMap V basis v x = ∑ i, (basis i).val x * v i := by
  change (basis.equivFun.symm v).val x = _
  rw [basis.equivFun_symm_apply]
  simp [mul_comm]

omit [Group G] [DecidableEq G] [DecidableEq ι] in
theorem basisFunctionsLinearMap_injective (V : Submodule ℝ (G → ℝ))
    (basis : Module.Basis ι ℝ V) : Function.Injective (basisFunctionsLinearMap V basis) :=
  Subtype.val_injective.comp basis.equivFun.symm.injective

omit [DecidableEq ι] in
theorem wordBallGram_quadratic (S : Finset G) (R : ℕ) (F : ι → G → ℝ) (v : ι → ℝ) :
    realMatrixQuadratic (wordBallGram S R F) v =
      ∑ x ∈ wordBall S R, (∑ i, F i x * v i) ^ 2 := by
  change v ⬝ᵥ (((wordBallEvaluationMatrix S R F)ᵀ * wordBallEvaluationMatrix S R F) *ᵥ v) = _
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  change (∑ x : wordBall S R, (∑ i, F i x.val * v i) * (∑ i, F i x.val * v i)) = _
  calc
    _ = ∑ x : wordBall S R, (∑ i, F i x.val * v i) ^ 2 := by
      apply sum_congr rfl
      intro x _
      exact (pow_two _).symm
    _ = _ := sum_coe_sort (wordBall S R) (fun x : G => (∑ i, F i x * v i) ^ 2)

omit [DecidableEq ι] in
theorem wordBallGram_basis_quadratic (S : Finset G) (R : ℕ)
    (V : Submodule ℝ (G → ℝ)) (basis : Module.Basis ι ℝ V) (v : ι → ℝ) :
    realMatrixQuadratic (wordBallGram S R (fun i => (basis i).val)) v =
      wordBallQuadraticValue S R (basisFunctionsLinearMap V basis v) := by
  simp only [wordBallGram_quadratic, wordBallQuadraticValue, basisFunctionsLinearMap_apply]

theorem exists_wordBall_controlled_subspace (S : Finset G)
    (V : Submodule ℝ (G → ℝ)) (basis : Module.Basis ι ℝ V)
    {m n : ℕ} (hmn : m ≤ n)
    (hpos : (wordBallGram S m (fun i => (basis i).val)).PosDef)
    (K : ℝ) (hK : 1 < K)
    (hdet : (wordBallGram S n (fun i => (basis i).val)).det ≤
      K ^ Fintype.card ι * (wordBallGram S m (fun i => (basis i).val)).det) :
    ∃ W : Submodule ℝ (G → ℝ), W ≤ V ∧ Module.finrank ℝ V ≤ 2 * Module.finrank ℝ W ∧
      ∀ f ∈ W, wordBallQuadraticValue S n f ≤ K ^ 2 * wordBallQuadraticValue S m f := by
  obtain ⟨W₀, hdim, hW₀⟩ := real_ordered_forms_large_subspace hpos
    (wordBallGram_sub_posSemidef S _ hmn) K hK hdet
  let L := basisFunctionsLinearMap V basis
  have hi : Function.Injective L := basisFunctionsLinearMap_injective V basis
  let W := W₀.map L
  have hW : W ≤ V := by
    intro f hf
    obtain ⟨v, _, rfl⟩ := Submodule.mem_map.mp hf
    exact (basis.equivFun.symm v).property
  have hd : Module.finrank ℝ W = Module.finrank ℝ W₀ :=
    (Submodule.equivMapOfInjective L hi W₀).finrank_eq.symm
  refine ⟨W, hW, ?_, ?_⟩
  · rw [hd, Module.finrank_eq_card_basis basis]
    exact hdim
  · intro f hf
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hf
    simpa only [wordBallGram_basis_quadratic] using hW₀ v hv

end PolycyclicRecognition

end

end OAI
