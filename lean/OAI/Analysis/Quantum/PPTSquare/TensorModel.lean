import OAI.Analysis.Quantum.PPTSquare.ChannelCompletion

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open scoped MatrixOrder
namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

def product {n m : Type} (u : n → ℂ) (v : m → ℂ) : n × m → ℂ :=
  fun a => u a.1 * v a.2

def projector {n : Type} (x : n → ℂ) : Mat n := Matrix.vecMulVec x (star x)

def hsAdjoint {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] (F : Map n m) : Map m n where
  toFun Y := Matrix.of fun i j => ∑ a, ∑ b, star (F (Matrix.single i j 1) a b) * Y a b
  map_add' X Y := by
    ext i j
    change (∑ a, ∑ b, star (F (Matrix.single i j 1) a b) * (X a b + Y a b)) =
      (∑ a, ∑ b, star (F (Matrix.single i j 1) a b) * X a b) +
      (∑ a, ∑ b, star (F (Matrix.single i j 1) a b) * Y a b)
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    change (∑ a, ∑ b, star (F (Matrix.single i j 1) a b) * (c * X a b)) =
      c * (∑ a, ∑ b, star (F (Matrix.single i j 1) a b) * X a b)
    simp [Finset.mul_sum, mul_left_comm]

def tensorMap {n m p q : Type} [Fintype n] [Fintype m] [Fintype p] [Fintype q]
    (F : Map n m) (G : Map p q) : Map (n × p) (m × q) where
  toFun X := Matrix.of fun a b =>
    F (Matrix.of fun i j => G (Matrix.of fun k l => X (i,k) (j,l)) a.2 b.2) a.1 b.1
  map_add' X Y := by
    ext a b
    have he : (Matrix.of fun i j => G (Matrix.of fun k l => (X + Y) (i,k) (j,l)) a.2 b.2) =
        (Matrix.of fun i j => G (Matrix.of fun k l => X (i,k) (j,l)) a.2 b.2) +
        (Matrix.of fun i j => G (Matrix.of fun k l => Y (i,k) (j,l)) a.2 b.2) := by
      ext i j
      change G ((Matrix.of fun k l => X (i,k) (j,l)) +
        (Matrix.of fun k l => Y (i,k) (j,l))) a.2 b.2 =
        (G (Matrix.of fun k l => X (i,k) (j,l)) + G (Matrix.of fun k l => Y (i,k) (j,l))) a.2 b.2
      rw [map_add]
    change F _ a.1 b.1 = (F _ + F _) a.1 b.1
    rw [he, map_add]
  map_smul' c X := by
    ext a b
    have he : (Matrix.of fun i j => G (Matrix.of fun k l => (c • X) (i,k) (j,l)) a.2 b.2) =
        c • (Matrix.of fun i j => G (Matrix.of fun k l => X (i,k) (j,l)) a.2 b.2) := by
      ext i j
      change G (c • (Matrix.of fun k l => X (i,k) (j,l))) a.2 b.2 =
        (c • G (Matrix.of fun k l => X (i,k) (j,l))) a.2 b.2
      rw [map_smul]
    change F _ a.1 b.1 = (c • F _) a.1 b.1
    rw [he, map_smul]

def symPair : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]

def altPair : Fin 6 → Fin 4 × Fin 4 := ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def rt : ℂ := (Real.sqrt 2 : ℝ)

def U : Matrix (Fin 4 × Fin 4) (Fin 10) ℂ := Matrix.of fun a t =>
  if (symPair t).1 = (symPair t).2 then
    if a = symPair t then 1 else 0
  else rt⁻¹ * ((if a = symPair t then 1 else 0) + (if a = (symPair t).swap then 1 else 0))

def V : Matrix (Fin 4 × Fin 4) (Fin 6) ℂ :=
  rt⁻¹ • (coord altPair - coord (fun i => (altPair i).swap))

def complement : Fin 6 → Fin 6 := ![5,4,3,2,1,0]
def complementSign : Fin 6 → ℂ := ![1,-1,1,1,-1,1]
def K : Mat (Fin 6) := Matrix.of fun i j => if i = complement j then complementSign j else 0

def E : Matrix (Fin 10) (Fin 6) ℂ := coord (fun i => ⟨i.val, by omega⟩)

def S (L : Map (Fin 4) (Fin 4)) : Map (Fin 10) (Fin 6) :=
  (ad Vᴴ).comp ((tensorMap L L).comp (ad U))
def R (L : Map (Fin 4) (Fin 4)) : Map (Fin 10) (Fin 6) :=
  (ad K).comp (transposeMap.comp (S L))

def Phi1 (L : Map (Fin 4) (Fin 4)) : Map (Fin 10) (Fin 10) :=
  (ad E).comp ((S L).comp transposeMap)
def Phi2 (L : Map (Fin 4) (Fin 4)) : Map (Fin 10) (Fin 10) :=
  (hsAdjoint (R L)).comp (ad Eᴴ)
def Z (L : Map (Fin 4) (Fin 4)) : Mat (Fin 10 × Fin 10) :=
  choi ((Phi2 L).comp (Phi1 L))

def DistinctDirections (X : Fin 20 → Fin 4 → ℂ) : Prop :=
  (∀ i, X i ≠ 0) ∧ ∀ i j, i ≠ j → ∀ c : ℂ, c ≠ 0 → X i ≠ c • X j

def QuadraticEvaluations (X : Fin 20 → Fin 4 → ℂ) : Prop :=
  ∀ p : MvPolynomial (Fin 4) ℂ, p.IsHomogeneous 2 → p ≠ 0 →
    (Finset.univ.filter (fun i => MvPolynomial.eval (X i) p = 0)).card ≤ 9

end TensorCriterion

namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

lemma rt_star : star rt = rt := by simp [rt]
lemma rt_ne : rt ≠ 0 := by
  unfold rt
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
lemma rt_sq : rt * rt = 2 := by
  unfold rt
  exact_mod_cast (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2))
lemma inv_rt_sq : rt⁻¹ * rt⁻¹ * 2 = 1 := by
  rw [← rt_sq]
  field_simp [rt_ne]

def compound (B : Mat (Fin 4)) : Mat (Fin 6) := Matrix.of fun i j =>
  B (altPair i).1 (altPair j).1 * B (altPair i).2 (altPair j).2 -
  B (altPair i).1 (altPair j).2 * B (altPair i).2 (altPair j).1

lemma V_compression (B : Mat (Fin 4)) : Vᴴ * (B ⊗ₖ B) * V = compound B := by
  simp only [V, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, star_inv₀, rt_star,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, coord_compress]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Prod.fst_swap, Prod.snd_swap, smul_eq_mul, compound,
    Matrix.of_apply]
  calc
    _ = (rt⁻¹ * rt⁻¹ * 2) *
      (B (altPair i).1 (altPair j).1 * B (altPair i).2 (altPair j).2 -
       B (altPair i).1 (altPair j).2 * B (altPair i).2 (altPair j).1) := by ring
    _ = _ := by rw [inv_rt_sq, one_mul]

lemma complement_involution (i : Fin 6) : complement (complement i) = i := by
  fin_cases i <;> rfl
lemma complement_sign (i : Fin 6) : complementSign (complement i) = complementSign i := by
  fin_cases i <;> rfl
lemma complement_sign_star (i : Fin 6) : star (complementSign i) = complementSign i := by
  fin_cases i <;> simp [complementSign]

lemma K_hermitian : Kᴴ = K := by
  ext i j
  simp only [K, Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite, star_zero, complement_sign_star]
  by_cases h : i = complement j
  · have hj : j = complement i := by rw [h, complement_involution]
    simp only [ite_eq_left h, ite_eq_left hj]
    rw [h, complement_sign]
  · have hj : j ≠ complement i := by
      intro hj
      apply h
      rw [hj, complement_involution]
    simp [h, hj]

lemma K_mul (A : Mat (Fin 6)) (i j : Fin 6) :
    (K * A) i j = complementSign i * A (complement i) j := by
  fin_cases i <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, K, complement, complementSign]

lemma mul_K (A : Mat (Fin 6)) (i j : Fin 6) :
    (A * K) i j = A i (complement j) * complementSign j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, K, complement, complementSign]

lemma exterior_dual_apply (A : Mat (Fin 6)) (i j : Fin 6) :
    (K * Aᵀ * Kᴴ) i j =
      complementSign i * complementSign j * A (complement j) (complement i) := by
  rw [K_hermitian, mul_K, K_mul]
  simp only [Matrix.transpose_apply]
  ring

lemma compound_pair_diagonal (B : Mat (Fin 4)) (i : Fin 6) :
    ∑ j, complementSign i * complementSign j *
      compound B (complement j) (complement i) * compound B j i = B.det := by
  rw [Matrix.det_succ_row_zero]
  fin_cases i <;>
    simp [Fin.sum_univ_succ, compound, altPair, complement, complementSign,
      Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove] <;> ring

lemma compound_pair_trace (B : Mat (Fin 4)) :
    Matrix.trace ((K * (compound B)ᵀ * Kᴴ) * compound B) = 6 * B.det := by
  change (∑ i, ∑ j, (K * (compound B)ᵀ * Kᴴ) i j * compound B j i) = 6 * B.det
  simp_rw [exterior_dual_apply, compound_pair_diagonal]
  simp

end TensorCriterion

end

end OAI
