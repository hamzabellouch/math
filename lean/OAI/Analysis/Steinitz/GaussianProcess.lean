import OAI.Analysis.Steinitz.Predictor

namespace OAI

/-! Stationary Gaussian autoregressive rows and covariance identities. -/

section

open Matrix
open scoped BigOperators
namespace GaussianAR

noncomputable def row (r : ℝ) : ℕ → ℕ → ℝ
  | 0,k => if k=0 then 1 else 0
  | t+1,k => r*row r t k + if k=t+1 then Real.sqrt (1-r^2) else 0

lemma row_support (r : ℝ) {t k : ℕ} (h : t<k) : row r t k=0 := by
  induction t with
  | zero => simp [row,show k≠0 by omega]
  | succ t ih => simp [row,ih (by omega),show k≠t+1 by omega]

lemma row_initial (r : ℝ) (t : ℕ) : row r t 0 = r^t := by
  induction t with
  | zero => simp [row]
  | succ t ih => simp [row,ih,pow_succ,mul_comm]

lemma row_diag (r : ℝ) (t : ℕ) : row r (t+1) (t+1) = Real.sqrt (1-r^2) := by
  simp [row,row_support r (Nat.lt_succ_self t)]

lemma row_dot_step (r : ℝ) (n t u : ℕ) (ht : t<n) :
    (∑ k ∈ Finset.range (n+1), row r (t+1) k*row r u k) =
      r*(∑ k ∈ Finset.range (n+1), row r t k*row r u k)+
        Real.sqrt (1-r^2)*row r u (t+1) := by
  simp only [row,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range,show t+1<n+1 by omega,ite_true]

lemma row_norm (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (n t : ℕ) (ht : t≤n) :
    (∑ k ∈ Finset.range (n+1), (row r t k)^2)=1 := by
  have hs : 0 ≤ 1-r^2 := by nlinarith
  induction t with
  | zero => simp [row]
  | succ t ih =>
    have hp := ih (by omega)
    have hcross : (∑ k ∈ Finset.range (n+1), row r t k*(if k=t+1 then Real.sqrt (1-r^2) else 0))=0 := by
      simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_range,show t+1<n+1 by omega,ite_true]
      rw [row_support r (by omega),zero_mul]
    have he (k : ℕ) : (row r (t+1) k)^2 = r^2*(row r t k)^2+
        2*r*(row r t k*(if k=t+1 then Real.sqrt (1-r^2) else 0))+
        (if k=t+1 then (Real.sqrt (1-r^2))^2 else 0) := by
      rw [row]
      split_ifs <;> ring
    simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,hp,hcross,mul_zero,add_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range,show t+1<n+1 by omega,ite_true,mul_one,Real.sq_sqrt hs]
    ring

lemma row_covariance (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (n t u : ℕ) (ht : t≤n) (hu : u≤t) :
    (∑ k ∈ Finset.range (n+1), row r t k*row r u k)=r^(t-u) := by
  induction t with
  | zero =>
    have : u=0 := by omega
    subst u
    simp [row]
  | succ t ih =>
    by_cases h : u=t+1
    · subst u
      simpa only [Nat.sub_self,pow_zero,← sq] using row_norm r hr hr1 n (t+1) ht
    · have hu' : u≤t := by omega
      rw [row_dot_step r n t u (by omega),ih (by omega) hu',row_support r (by omega),mul_zero,add_zero]
      rw [show t+1-u=(t-u)+1 by omega,pow_succ,mul_comm]

lemma row_norm_fin (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (n : ℕ) (t : Fin (n+1)) :
    (∑ k : Fin (n+1), (row r t.val k.val)^2)=1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (row r t.val k)^2)]
  exact row_norm r hr hr1 n t.val (by omega)

lemma row_covariance_fin (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (n : ℕ) (t u : Fin (n+1)) (hu : u≤t) :
    (∑ k : Fin (n+1), row r t.val k.val*row r u.val k.val)=r^(t.val-u.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => row r t.val k*row r u.val k)]
  exact row_covariance r hr hr1 n t.val u.val (by omega) hu

lemma one_sub_pow_le (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (t : ℕ) :
    1-r^t ≤ t*(1-r) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    have hp : r^t≤1 := pow_le_one₀ hr hr1
    nlinarith

end GaussianAR

end

section

open Matrix
open scoped BigOperators RealInnerProductSpace
namespace GaussianTail
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
lemma trace_covariance (B : Matrix κ ι ℝ) : (B*B.transpose).trace=squareMass B := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,squareMass,← sq]

lemma squareMass_mul_covariance (B : Matrix κ ι ℝ) (C : Matrix ι ν ℝ) :
    squareMass (B*C) = (B*(C*C.transpose)*B.transpose).trace := by
  rw [← trace_covariance,Matrix.transpose_mul]
  congr 1
  simp only [Matrix.mul_assoc]

lemma squareMass_add_le (B C : Matrix κ ι ℝ) :
    squareMass (B+C) ≤ 2*squareMass B+2*squareMass C := by
  unfold squareMass
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,Matrix.add_apply]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  nlinarith [sq_nonneg (B i k-C i k)]

lemma squareMass_neg (B : Matrix κ ι ℝ) : squareMass (-B)=squareMass B := by
  simp [squareMass]

end GaussianTail
namespace GaussianAR
open GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def evaluation (r : ι → ℝ) (n : ℕ) (t : Fin (n+1)) : Matrix ι (Fin (n+1)×ι) ℝ :=
  fun i k => if i=k.2 then row (r i) t.val k.1.val else 0

lemma evaluation_mul_transpose (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (t u : Fin (n+1)) (hu : u≤t) :
    evaluation r n t*(evaluation r n u).transpose = diagonal (fun i => (r i)^(t.val-u.val)) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,evaluation]
  by_cases hij : i=j
  · subst j
    simp only [mul_ite,ite_mul,mul_zero,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Matrix.diagonal_apply_eq]
    exact row_covariance_fin (r i) (hr i) (hr1 i) n t u hu
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    split_ifs <;> simp_all

lemma evaluation_coisometry (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (t : Fin (n+1)) :
    evaluation r n t*(evaluation r n t).transpose=1 := by
  rw [evaluation_mul_transpose r hr hr1 n t t le_rfl]
  simp

lemma evaluation_cross_symmetric (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (t u : Fin (n+1)) :
    evaluation r n t*(evaluation r n u).transpose = evaluation r n u*(evaluation r n t).transpose := by
  rcases le_total u t with h|h
  · have ht : (evaluation r n t*(evaluation r n u).transpose).transpose =
        evaluation r n t*(evaluation r n u).transpose := by
      rw [evaluation_mul_transpose r hr hr1 n t u h,Matrix.diagonal_transpose]
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using ht.symm
  · have ht : (evaluation r n u*(evaluation r n t).transpose).transpose =
        evaluation r n u*(evaluation r n t).transpose := by
      rw [evaluation_mul_transpose r hr hr1 n u t h,Matrix.diagonal_transpose]
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using ht

lemma evaluation_difference_covariance (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (t u : Fin (n+1)) (hu : u≤t) :
    (evaluation r n t-evaluation r n u)*(evaluation r n t-evaluation r n u).transpose =
      diagonal (fun i => 2*(1-(r i)^(t.val-u.val))) := by
  rw [Matrix.transpose_sub,Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mul,
    evaluation_coisometry r hr hr1,evaluation_coisometry r hr hr1,
    ← evaluation_cross_symmetric r hr hr1 n t u,evaluation_mul_transpose r hr hr1 n t u hu]
  ext i j
  by_cases h : i=j
  · subst j; simp; ring
  · simp [h]

lemma squareMass_evaluation {κ : Type*} [Fintype κ] (B : Matrix κ ι ℝ)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1) (n : ℕ) (t : Fin (n+1)) :
    squareMass (B*evaluation r n t)=squareMass B := by
  rw [squareMass_mul_covariance,evaluation_coisometry r hr hr1,Matrix.mul_one,trace_covariance]

lemma trace_weighted_square {κ : Type*} [Fintype κ] (B : Matrix κ ι ℝ) (w : ι → ℝ) :
    (B*diagonal w*B.transpose).trace = ∑ i,∑ j,(B i j)^2*w j := by
  change (∑ i,∑ j,(B*diagonal w) i j*B i j) = _
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma squareMass_time_le {κ : Type*} [Fintype κ] (B : Matrix κ ι ℝ)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1) (n : ℕ) (t u : Fin (n+1)) :
    squareMass (B*(evaluation r n t-evaluation r n u)) ≤
      2*|(t.val:ℝ)-u.val| * (B*diagonal (fun i => 1-r i)*B.transpose).trace := by
  wlog hu : u≤t generalizing t u
  · have h := this u t (le_of_not_ge hu)
    rw [show evaluation r n t-evaluation r n u= -(evaluation r n u-evaluation r n t) by abel,
      Matrix.mul_neg,squareMass_neg,abs_sub_comm]
    exact h
  rw [squareMass_mul_covariance,evaluation_difference_covariance r hr hr1 n t u hu,
    trace_weighted_square,trace_weighted_square,abs_of_nonneg (sub_nonneg.mpr (show (u.val:ℝ) ≤ t.val by exact_mod_cast hu)),
    ← Nat.cast_sub hu]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := one_sub_pow_le (r j) (hr j) (hr1 j) (t.val-u.val)
  nlinarith [mul_nonneg (sq_nonneg (B i j)) (sub_nonneg.mpr h)]

end GaussianAR

end

end OAI
