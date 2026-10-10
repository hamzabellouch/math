import Mathlib
import OAI.Analysis.LaughlinGap.CovariantLift
import OAI.Analysis.LaughlinGap.SpinAveraging

namespace OAI

/-! Covariant Family. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

omit [DecidableEq ι] in
lemma Covariant.combination_lower [DecidableEq ι] {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (x : ι → ℝ) :
    commutator L (combination B x) = -combination B (D.transpose.mulVec x) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    h.lower, smul_neg, Finset.smul_sum, smul_smul, Finset.sum_neg_distrib,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

lemma Covariant.combination_raise {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (x : ι → ℝ) :
    commutator L.transpose (combination B x) = -combination B (D.mulVec x) := by
  simpa using h.transpose.combination_lower x

noncomputable def embeddingFamily {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (B : κ → Matrix σ σ ℝ) : ι → Matrix σ σ ℝ :=
  fun i => combination B (A.toLinearMap (Pi.single i 1))

omit [DecidableEq κ] [Fintype σ] [DecidableEq σ] in
lemma combination_embeddingFamily [DecidableEq κ] [Fintype σ] [DecidableEq σ]
    {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (B : κ → Matrix σ σ ℝ) (x : ι → ℝ) :
    combination (embeddingFamily A B) x = combination B (A.toLinearMap x) := by
  rw [A.toLinearMap.pi_apply_eq_sum_univ x, map_sum]
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, embeddingFamily, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : (Pi.single i 1 : ι → ℝ) = (fun j => if i=j then 1 else 0) := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [hs]

lemma Covariant.embedding {L : Matrix σ σ ℝ} {S : LadderSystem ι}
    {T : LadderSystem κ} {B : κ → Matrix σ σ ℝ}
    (h : Covariant L (loweringMatrix T) B) (A : LadderMap S T) :
    Covariant L (loweringMatrix S) (embeddingFamily A B) where
  lower i := by
    change commutator L (combination B _) = _
    rw [h.combination_lower, loweringMatrix_transpose, LinearMap.toMatrix'_mulVec]
    change -combination B (T.raise (A.toLinearMap (Pi.single i 1))) = _
    rw [A.raise, ← combination_embeddingFamily]
    congr 1
    simp only [combination, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have he := congrArg (fun M : Matrix ι ι ℝ => M j i) (loweringMatrix_transpose S)
    simpa only [Matrix.transpose_apply, loweringMatrix, LinearMap.toMatrix'_apply] using he.symm
  raise i := by
    change commutator L.transpose (combination B _) = _
    rw [h.combination_raise, loweringMatrix, LinearMap.toMatrix'_mulVec]
    change -combination B (T.lower (A.toLinearMap (Pi.single i 1))) = _
    rw [A.lower, ← combination_embeddingFamily]
    rfl

noncomputable def productFamily (B : ι → Matrix σ σ ℝ) (C : κ → Matrix σ σ ℝ) :
    (ι × κ) → Matrix σ σ ℝ := fun ij => C ij.2 * B ij.1

lemma loweringMatrix_tensor (S : LadderSystem ι) (T : LadderSystem κ)
    (i j : ι × κ) :
    loweringMatrix (S.tensor T) i j =
      (if i.2=j.2 then loweringMatrix S i.1 j.1 else 0) +
      (if i.1=j.1 then loweringMatrix T i.2 j.2 else 0) := by
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  simp only [loweringMatrix, LinearMap.toMatrix'_apply, LadderSystem.tensor,
    LinearMap.add_apply, onFirstEnd_apply, onSecondEnd_apply, Pi.add_apply]
  have hf : (fun a : ι => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (a,i₂)) =
      if i₂=j₂ then Pi.single j₁ 1 else 0 := by
    funext a
    by_cases he : i₂=j₂ <;> simp [he, Pi.single_apply, Prod.mk.injEq, eq_comm]
  have hs : (fun a : κ => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (i₁,a)) =
      if i₁=j₁ then Pi.single j₂ 1 else 0 := by
    funext a
    by_cases he : i₁=j₁ <;> simp [he, Pi.single_apply, Prod.mk.injEq, eq_comm]
  change S.lower (fun a => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (a,i₂)) i₁ +
    T.lower (fun a => (Pi.single (j₁,j₂) (1 : ℝ) : (ι × κ) → ℝ) (i₁,a)) i₂ = _
  rw [hf, hs]
  split_ifs <;> simp_all

lemma product_commutator {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ} {E : Matrix κ κ ℝ}
    {B : ι → Matrix σ σ ℝ} {C : κ → Matrix σ σ ℝ}
    (hB : ∀ i, commutator L (B i) = -∑ j, D i j • B j)
    (hC : ∀ i, commutator L (C i) = -∑ j, E i j • C j) (i : ι × κ) :
    commutator L (productFamily B C i) =
      -∑ j : ι × κ, ((if i.2=j.2 then D i.1 j.1 else 0) +
        (if i.1=j.1 then E i.2 j.2 else 0)) • productFamily B C j := by
  simp only [productFamily, commutator_mul, hB, hC, neg_mul, Matrix.mul_neg,
    Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm,
    Fintype.sum_prod_type, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, Finset.sum_const_zero, Finset.sum_ite_eq]
  abel

lemma Covariant.product {L : Matrix σ σ ℝ} {S : LadderSystem ι} {T : LadderSystem κ}
    {B : ι → Matrix σ σ ℝ} {C : κ → Matrix σ σ ℝ}
    (hB : Covariant L (loweringMatrix S) B) (hC : Covariant L (loweringMatrix T) C) :
    Covariant L (loweringMatrix (S.tensor T)) (productFamily B C) where
  lower i := by simpa only [loweringMatrix_tensor] using product_commutator hB.lower hC.lower i
  raise i := by
    simpa only [Matrix.transpose_apply, loweringMatrix_tensor, eq_comm] using
      product_commutator hB.transpose.lower hC.transpose.lower i

omit [DecidableEq ι] in
lemma Covariant.smul [DecidableEq ι] {L : Matrix σ σ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix σ σ ℝ} (h : Covariant L D B) (r : ℝ) :
    Covariant L D (fun i => r • B i) where
  lower i := by simp only [map_smul, h.lower, smul_neg, Finset.smul_sum, smul_comm r]
  raise i := by simp only [map_smul, h.raise, smul_neg, Finset.smul_sum, smul_comm r]

end LaughlinGap.RealOccupation

end

end OAI
