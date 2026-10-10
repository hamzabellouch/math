import Mathlib
import OAI.Analysis.MatrixSigning.Potential.QuadGram
import OAI.Analysis.MatrixSigning.Potential.WhitenWeighted

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Covariance

section
open Matrix WithLp
open scoped BigOperators

variable {n m : ℕ}

def pairIndex (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2*n) :=
  finSumFinEquiv.trans (finCongr (by omega))

def offBlock (A B : Mat n) : Mat (2*n) :=
  Matrix.reindex (pairIndex n) (pairIndex n) (Matrix.fromBlocks 0 B A 0)

lemma offBlock_gram_trace (A B : Mat n) :
    ((offBlock A B).conjTranspose*offBlock A B).trace =
      (A.conjTranspose*A).trace+(B.conjTranspose*B).trace := by
  rw [gram_trace,gram_trace,gram_trace]
  simp only [offBlock,Matrix.reindex_apply,Matrix.submatrix_apply]
  have hm (D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
      (∑ i : Fin (2*n), ∑ j : Fin (2*n), (D ((pairIndex n).symm i) ((pairIndex n).symm j))^2) =
        ∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n, (D i j)^2 := by
    calc
      _ = ∑ i : Fin (2*n), ∑ j : Fin n ⊕ Fin n, (D ((pairIndex n).symm i) j)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact (pairIndex n).symm.sum_comp (fun j : Fin n ⊕ Fin n => (D ((pairIndex n).symm i) j)^2)
      _ = _ := (pairIndex n).symm.sum_comp (fun i : Fin n ⊕ Fin n => ∑ j : Fin n ⊕ Fin n, (D i j)^2)
  rw [hm]
  simp only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero,zero_add,add_zero]
  ac_rfl

def weightEquiv (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) : E m ≃ₗ[ℝ] E m :=
  (EuclideanSpace.equiv (Fin m) ℝ).toLinearEquiv |>.trans
    (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (a i))
      (ne_of_gt (Real.sqrt_pos.mpr (ha i)))) |>.trans
        (EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearEquiv

lemma weightEquiv_apply (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (x : E m) (i : Fin m) :
    weightEquiv a ha x i = Real.sqrt (a i)*x i := by rfl

lemma whiten_mul_weight (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (M : Mat m) (x : E m) :
    (whitenWeighted a b M).toEuclideanLin (weightEquiv a ha x) =
      weightEquiv b hb (M.toEuclideanLin x) := by
  ext i
  change (∑ j, whitenWeighted a b M i j * (weightEquiv a ha x) j) =
    Real.sqrt (b i)*(∑ j, M i j*x j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [whitenWeighted,weightEquiv_apply]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (ha j))]

lemma combined_weighted_response {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (W : V →L[ℝ] V) (M : V →L[ℝ] V) (x y : V)
    (he : x = y+M x) (hc : ‖W (M x)‖^2 ≤ (1/4 : ℝ)*‖W x‖^2) :
    ‖W x‖^2 ≤ 4*‖W y‖^2 := by
  have hq : ‖W (M x)‖ ≤ ‖W x‖/2 := by
    nlinarith [norm_nonneg (W x),norm_nonneg (W (M x))]
  have ht : ‖W x‖ ≤ ‖W y‖+‖W (M x)‖ := by
    calc
      _ = ‖W y+W (M x)‖ := by rw [← map_add,← he]
      _ ≤ _ := norm_add_le _ _
  have hnorm : ‖W x‖ ≤ 2*‖W y‖ := by linarith
  nlinarith [norm_nonneg (W x),norm_nonneg (W y)]

end

open Matrix WithLp
open scoped BigOperators

local instance : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace
variable {n : ℕ}

def pairWeight (a b : Fin n → ℝ) : Fin (2*n) → ℝ :=
  Sum.elim a b ∘ (pairIndex n).symm

lemma pairWeight_pos (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∀ i, 0 < pairWeight a b i := by
  intro i
  dsimp only [pairWeight,Function.comp_apply]
  cases (pairIndex n).symm i with
  | inl j => exact ha j
  | inr j => exact hb j

lemma whiten_offBlock (a b : Fin n → ℝ) (A B : Mat n) :
    whitenWeighted (pairWeight a b) (pairWeight a b) (offBlock A B) =
      offBlock (whitenWeighted a b A) (whitenWeighted b a B) := by
  ext i j
  simp only [whitenWeighted,offBlock,Matrix.reindex_apply,Matrix.submatrix_apply,pairWeight,
    Function.comp_apply]
  cases (pairIndex n).symm i <;> cases (pairIndex n).symm j <;>
    simp only [Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply,mul_zero,zero_div] <;> rfl

lemma whiten_offBlock_gram (a b : Fin n → ℝ) (A B : Mat n)
    (hA : ((whitenWeighted a b A).conjTranspose*whitenWeighted a b A).trace ≤ (n : ℝ)/384)
    (hB : ((whitenWeighted b a B).conjTranspose*whitenWeighted b a B).trace ≤ (n : ℝ)/384) :
    let C := whitenWeighted (pairWeight a b) (pairWeight a b) (offBlock A B)
    (C.conjTranspose*C).trace ≤ (2*n : ℝ)/384 := by
  dsimp only
  rw [whiten_offBlock,offBlock_gram_trace]
  linarith

theorem weighted_block_covariance (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A B : Mat n) (L : E (2*n) →ₗ[ℝ] E n)
    (hA : ((whitenWeighted a b A).conjTranspose*whitenWeighted a b A).trace ≤ (n : ℝ)/384)
    (hB : ((whitenWeighted b a B).conjTranspose*whitenWeighted b a B).trace ≤ (n : ℝ)/384) :
    ∃ Γ : Mat (2*n), Γ.PosSemidef ∧
      (∀ i, Γ i i ≤ 1) ∧ (slack 4 Γ).PosSemidef ∧ (23/48 : ℝ)*n ≤ Γ.trace ∧
      (∀ x, L (Γ.toEuclideanLin x) = 0) ∧
      ∀ x, ‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb)
        ((offBlock A B).toEuclideanLin (Γ.toEuclideanLin x))‖^2 ≤
        (1/4 : ℝ)*‖weightEquiv (pairWeight a b) (pairWeight_pos a b ha hb) (Γ.toEuclideanLin x)‖^2 := by
  let D := pairWeight a b
  have hD := pairWeight_pos a b ha hb
  obtain ⟨Γ,hΓ,hd,hs,ht,hL,hq⟩ := coupled_covariance
    (whitenWeighted D D (offBlock A B)) (weightEquiv D hD) L (whiten_offBlock_gram a b A B hA hB)
  refine ⟨Γ,hΓ,hd,hs,ht,hL,?_⟩
  intro x
  have hh := hq x
  rw [whiten_mul_weight D D hD hD] at hh
  simpa only [real_inner_self_eq_norm_sq] using hh

end CurrentKS.Covariance

end

end OAI
