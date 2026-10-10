import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RationalPSDDecision

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

structure Pencil (n m : ℕ) where
  constant : Matrix (Fin m) (Fin m) ℚ
  coeff : Fin n → Matrix (Fin m) (Fin m) ℚ
  symmetric_constant : constant.IsSymm
  symmetric_coeff : ∀ i, (coeff i).IsSymm

variable {n m : ℕ}

def Pencil.eval (B : Pencil n m) (y : Fin n → ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  B.constant + ∑ i, y i • B.coeff i

noncomputable def Pencil.realEval (B : Pencil n m) (y : Fin n → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  B.constant.map (fun x => (x : ℝ)) + ∑ i, y i • (B.coeff i).map (fun x => (x : ℝ))

lemma Pencil.eval_symmetric (B : Pencil n m) (y : Fin n → ℚ) : (B.eval y).IsSymm := by
  unfold Pencil.eval
  apply Matrix.IsSymm.ext
  intro i j
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [B.symmetric_constant.apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [(B.symmetric_coeff k).apply]

lemma Pencil.cast_eval (B : Pencil n m) (y : Fin n → ℚ) :
    (B.eval y).map (fun x => (x : ℝ)) = B.realEval (fun i => (y i : ℝ)) := by
  ext i j
  simp [Pencil.eval,Pencil.realEval,Matrix.sum_apply,Rat.cast_sum]

def Pencil.witness (B : Pencil n m) (y : Fin n → ℚ) : Option (Fin m → ℚ) :=
  KS.W17.rationalNegativeWitness m (B.eval y)

def Pencil.normal (B : Pencil n m) (v : Fin m → ℚ) : Fin n → ℚ :=
  fun i => KS.W17.psdCutEval v (B.coeff i)

def Pencil.offset (B : Pencil n m) (v : Fin m → ℚ) : ℚ :=
  - KS.W17.psdCutEval v B.constant

lemma Pencil.quadratic_eval (B : Pencil n m) (v : Fin m → ℚ) (y : Fin n → ℚ) :
    KS.W17.psdCutEval v (B.eval y) = B.normal v ⬝ᵥ y - B.offset v := by
  unfold Pencil.normal Pencil.offset
  simp only [KS.W17.psdCutEval,Pencil.eval,Matrix.add_mulVec,
    Matrix.sum_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_sum,dotProduct_smul,
    smul_eq_mul]
  simp only [dotProduct,neg_mul,Finset.sum_neg_distrib]
  rw [show (∑ i, y i * (∑ j,v j*(B.coeff i *ᵥ v) j)) =
      ∑ i, (∑ j,v j*(B.coeff i *ᵥ v) j)*y i by
    apply Finset.sum_congr rfl; intro i _; ring]
  ring

lemma Pencil.quadratic_realEval (B : Pencil n m) (v : Fin m → ℚ) (y : Fin n → ℝ) :
    KS.W17.psdCutEvalReal v (B.realEval y) =
      (fun i => (B.normal v i : ℝ)) ⬝ᵥ y - (B.offset v : ℝ) := by
  unfold Pencil.realEval
  simp only [KS.W17.psdCutEvalReal,Matrix.add_mulVec,Matrix.sum_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_sum,dotProduct_smul,smul_eq_mul]
  have hc : (fun i => (v i : ℝ)) ⬝ᵥ
      (B.constant.map (fun x : ℚ => (x : ℝ)) *ᵥ (fun i => (v i : ℝ))) =
      (B.offset v : ℝ) := by
    simp [Pencil.offset,KS.W17.psdCutEval,dotProduct,Matrix.mulVec,Rat.cast_sum]
  have hi (i : Fin n) : (fun j => (v j : ℝ)) ⬝ᵥ
      ((B.coeff i).map (fun x : ℚ => (x : ℝ)) *ᵥ (fun j => (v j : ℝ))) =
      -(B.normal v i : ℝ) := by
    simp [Pencil.normal,KS.W17.psdCutEval,dotProduct,Matrix.mulVec,Rat.cast_sum]
  rw [hc]
  simp_rw [hi]
  simp only [dotProduct,mul_neg,Finset.sum_neg_distrib]
  rw [show (∑ i, y i * (B.normal v i : ℝ)) = ∑ i, (B.normal v i : ℝ)*y i by
    apply Finset.sum_congr rfl; intro i _; ring]
  ring

lemma Pencil.witness_none_iff (B : Pencil n m) (y : Fin n → ℚ) :
    B.witness y = none ↔ (B.realEval (fun i => (y i : ℝ))).PosSemidef := by
  rw [Pencil.witness,KS.W17.rationalNegativeWitness_none_iff_psd _ _ (B.eval_symmetric y),
    B.cast_eval]

lemma Pencil.witness_some (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) :
    B.offset v < B.normal v ⬝ᵥ y ∧
      ∀ z : Fin n → ℝ, (B.realEval z).PosSemidef →
        (fun i => (B.normal v i : ℝ)) ⬝ᵥ z ≤ (B.offset v : ℝ) := by
  constructor
  · have h := KS.W17.rationalNegativeWitness_sound _ _ (B.eval_symmetric y) v hv
    have h' : 0 < KS.W17.psdCutEval v (B.eval y) := neg_pos.mpr h
    rw [B.quadratic_eval] at h'
    linarith
  · intro z hz
    have h := KS.W17.psdCutEvalReal_nonpos v _ hz
    rw [B.quadratic_realEval] at h
    linarith

lemma Pencil.normal_ne_zero (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) (z : Fin n → ℝ) (hz : (B.realEval z).PosSemidef) :
    B.normal v ≠ 0 := by
  intro hzero
  obtain ⟨h₁,h₂⟩ := B.witness_some y v hv
  have h₂ := h₂ z hz
  rw [hzero,zero_dotProduct] at h₁
  have hzero' : (fun i => (B.normal v i : ℝ)) = 0 := by funext i; simp [hzero]
  rw [hzero',zero_dotProduct] at h₂
  exact (not_lt_of_ge h₂) (by exact_mod_cast h₁)

lemma Pencil.central_cut (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) (z : Fin n → ℝ) (hz : (B.realEval z).PosSemidef) :
    (fun i => (B.normal v i : ℝ)) ⬝ᵥ (z - fun i => (y i : ℝ)) ≤ 0 := by
  obtain ⟨h₁,h₂⟩ := B.witness_some y v hv
  have h₂ := h₂ z hz
  have h₁' : (B.offset v : ℝ) <
      (fun i => (B.normal v i : ℝ)) ⬝ᵥ (fun i => (y i : ℝ)) := by
    simpa [dotProduct,Rat.cast_sum] using (Rat.cast_lt (K := ℝ)).mpr h₁
  rw [dotProduct_sub]
  linarith

end CurrentKS.RationalSDP

end OAI
