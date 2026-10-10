import Mathlib
import OAI.Analysis.LaughlinFock.Model

namespace OAI

/-! Sphere Scaling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
def occupationDiagonal (Q : ℕ) (d : Orbital Q → ℂ) : FockMatrix Q :=
  Matrix.diagonal (fun A => ∏ j ∈ A, d j)

 
def occupationDiagonalInv (Q : ℕ) (d : Orbital Q → ℂ) : FockMatrix Q :=
  Matrix.diagonal (fun A => (∏ j ∈ A, d j)⁻¹)

theorem occupationDiagonal_inv_mul (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) :
    occupationDiagonalInv Q d * occupationDiagonal Q d = 1 := by
  simp only [occupationDiagonalInv, occupationDiagonal, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 1
  congr 1
  funext A
  exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))

theorem occupationDiagonal_mul_inv (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) :
    occupationDiagonal Q d * occupationDiagonalInv Q d = 1 := by
  simp only [occupationDiagonalInv, occupationDiagonal, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 1
  congr 1
  funext A
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))

 
theorem annihilator_mul_occupationDiagonal (Q : ℕ) (d : Orbital Q → ℂ)
    (j : Orbital Q) :
    annihilator Q j * occupationDiagonal Q d =
      d j • (occupationDiagonal Q d * annihilator Q j) := by
  ext A B
  simp only [occupationDiagonal, Matrix.mul_diagonal, Matrix.smul_apply,
    Matrix.diagonal_mul, smul_eq_mul]
  by_cases h : j ∈ B ∧ A = B.erase j
  · obtain ⟨hj, rfl⟩ := h
    simp only [annihilator, hj, and_self, ite_true]
    rw [← Finset.mul_prod_erase B d hj]
    ring
  · simp [annihilator, h]

 
def diagonalConjugate (Q : ℕ) (d : Orbital Q → ℂ) (A : FockMatrix Q) : FockMatrix Q :=
  occupationDiagonalInv Q d * A * occupationDiagonal Q d

theorem diagonalConjugate_annihilator (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (j : Orbital Q) :
    diagonalConjugate Q d (annihilator Q j) = d j • annihilator Q j := by
  rw [diagonalConjugate, Matrix.mul_assoc, annihilator_mul_occupationDiagonal,
    Matrix.mul_smul, ← Matrix.mul_assoc, occupationDiagonal_inv_mul Q d hd,
    Matrix.one_mul]

theorem diagonalConjugate_mul (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (A B : FockMatrix Q) :
    diagonalConjugate Q d (A * B) =
      diagonalConjugate Q d A * diagonalConjugate Q d B := by
  symm
  unfold diagonalConjugate
  calc
    _ = occupationDiagonalInv Q d * A *
        (occupationDiagonal Q d * occupationDiagonalInv Q d) * B *
        occupationDiagonal Q d := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [occupationDiagonal_mul_inv Q d hd]; simp only [Matrix.mul_one,
      Matrix.mul_assoc]

theorem diagonalConjugate_sum (Q : ℕ) (d : Orbital Q → ℂ) {ι : Type*}
    (s : Finset ι) (A : ι → FockMatrix Q) :
    diagonalConjugate Q d (∑ i ∈ s, A i) = ∑ i ∈ s, diagonalConjugate Q d (A i) := by
  simp only [diagonalConjugate, Matrix.mul_sum, Matrix.sum_mul]

theorem diagonalConjugate_smul (Q : ℕ) (d : Orbital Q → ℂ) (a : ℂ) (A : FockMatrix Q) :
    diagonalConjugate Q d (a • A) = a • diagonalConjugate Q d A := by
  simp only [diagonalConjugate, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem diagonalConjugate_zero (Q : ℕ) (d : Orbital Q → ℂ) :
    diagonalConjugate Q d 0 = 0 := by simp [diagonalConjugate]

 
def coefficientPairAnnihilator (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) : FockMatrix Q :=
  ∑ i : Orbital Q, ∑ j : Orbital Q,
    if i < j then a i j • (annihilator Q j * annihilator Q i) else 0

theorem pairAnnihilator_eq_coefficientPairAnnihilator (Q p : ℕ) :
    pairAnnihilator Q p =
      coefficientPairAnnihilator Q (fun i j => (pairCoefficient Q p i j : ℂ)) := rfl

 
theorem diagonalConjugate_pair (Q : ℕ) (d : Orbital Q → ℂ)
    (hd : ∀ j, d j ≠ 0) (a : Orbital Q → Orbital Q → ℂ) :
    diagonalConjugate Q d (coefficientPairAnnihilator Q a) =
      coefficientPairAnnihilator Q (fun i j => a i j * d i * d j) := by
  unfold coefficientPairAnnihilator
  rw [diagonalConjugate_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalConjugate_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [diagonalConjugate_smul, diagonalConjugate_mul Q d hd,
      diagonalConjugate_annihilator Q d hd, diagonalConjugate_annihilator Q d hd,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    ring
  · exact diagonalConjugate_zero Q d

open Filter Topology

 
def scaledDescFactorial (Q s p : ℕ) : ℝ :=
  ((Q-s).descFactorial p : ℝ) / (Q : ℝ)^p

theorem scaledDescFactorial_nonneg (Q s p : ℕ) :
    0 ≤ scaledDescFactorial Q s p := by unfold scaledDescFactorial; positivity

theorem scaledDescFactorial_pos {Q s p : ℕ} (hQ : 0 < Q) (hp : p ≤ Q-s) :
    0 < scaledDescFactorial Q s p := by
  unfold scaledDescFactorial
  exact div_pos (by exact_mod_cast Nat.descFactorial_pos.mpr hp)
    (pow_pos (by exact_mod_cast hQ) _)

theorem scaledDescFactorial_le_one {Q : ℕ} (hQ : 0 < Q) (s p : ℕ) :
    scaledDescFactorial Q s p ≤ 1 := by
  unfold scaledDescFactorial
  rw [div_le_one (pow_pos (by exact_mod_cast hQ) _)]
  exact_mod_cast (Nat.descFactorial_le_pow (Q-s) p).trans
    (Nat.pow_le_pow_left (Nat.sub_le Q s) p)

theorem scaledDescFactorial_succ {Q s p : ℕ} (hQ : 0 < Q) (hs : s ≤ Q)
    (hp : p ≤ Q-s) :
    scaledDescFactorial Q s (p+1) =
      (1 - ((s : ℝ)+p)/Q) * scaledDescFactorial Q s p := by
  unfold scaledDescFactorial
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hp, Nat.cast_sub hs,
    pow_succ', mul_div_mul_comm]
  congr 1
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ)
  field_simp
  ring

theorem scaledDescFactorial_tendsto (s p : ℕ) :
    Tendsto (fun Q : ℕ => scaledDescFactorial Q s p) atTop (𝓝 1) := by
  induction p with
  | zero => simpa only [scaledDescFactorial, Nat.descFactorial_zero,
      Nat.cast_one, pow_zero, div_one] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  | succ p ih =>
    have hf : Tendsto (fun Q : ℕ => 1 - ((s:ℝ)+p)/Q) atTop (𝓝 1) := by
      convert (tendsto_const_nhds (x := (1:ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat ((s:ℝ)+p)) using 1
      norm_num
    have ht := hf.mul ih
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (s+p+1)] with Q hQ
    exact (scaledDescFactorial_succ (by omega) (by omega) (by omega)).symm

 
def modeScale (Q x : ℕ) : ℝ := Real.sqrt (scaledDescFactorial Q 0 x)

 
def pairScale (Q p : ℕ) : ℝ := Real.sqrt ((scaledDescFactorial (2*Q) 2 p)⁻¹)

theorem modeScale_nonneg (Q x : ℕ) : 0 ≤ modeScale Q x := Real.sqrt_nonneg _

theorem modeScale_pos {Q x : ℕ} (hQ : 0 < Q) (hx : x ≤ Q) :
    0 < modeScale Q x := by
  apply Real.sqrt_pos.mpr
  exact scaledDescFactorial_pos hQ (by simpa using hx)

theorem modeScale_le_one {Q : ℕ} (hQ : 0 < Q) (x : ℕ) : modeScale Q x ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  exact scaledDescFactorial_le_one hQ 0 x

theorem modeScale_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => modeScale Q x) atTop (𝓝 1) := by
  simpa only [modeScale, Real.sqrt_one] using (scaledDescFactorial_tendsto 0 x).sqrt

theorem pairScale_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => pairScale Q p) atTop (𝓝 1) := by
  have hd : Tendsto (fun Q : ℕ => 2*Q) atTop atTop :=
    tendsto_atTop_mono (fun Q => by change Q ≤ 2*Q; omega) tendsto_id
  have h := ((scaledDescFactorial_tendsto 2 p).comp hd).inv₀ (by norm_num : (1:ℝ) ≠ 0)
  simpa only [pairScale, inv_one, Real.sqrt_one, Function.comp_apply] using h.sqrt

theorem pairScale_one_le {Q p : ℕ} (hQ : 0 < Q) (hp : p ≤ 2*Q-2) :
    1 ≤ pairScale Q p := by
  apply Real.one_le_sqrt.mpr
  have hpos := scaledDescFactorial_pos (by omega : 0 < 2*Q) hp
  rw [one_le_inv₀ hpos]
  exact scaledDescFactorial_le_one (by omega) 2 p

 
def limitPairCoefficient (p i j : ℕ) : ℝ :=
  if i+j=p+1 then
    ((i:ℝ)-(j:ℝ)) * Real.sqrt ((p.factorial:ℝ) / (2^p * i.factorial * j.factorial))
  else 0

 
def sphericalPairCoefficient (Q p i j : ℕ) : ℝ :=
  if i+j=p+1 then
    ((i:ℝ)-(j:ℝ)) * Real.sqrt
      (((Q.descFactorial i:ℝ)*(Q.descFactorial j:ℝ)*(p.factorial:ℝ)) /
       ((Q:ℝ)*((2*Q-2).descFactorial p:ℝ)*(i.factorial:ℝ)*(j.factorial:ℝ)))
  else 0

theorem pairCoefficient_eq_sphericalPairCoefficient (Q p : ℕ) (i j : Orbital Q) :
    pairCoefficient Q p i j = sphericalPairCoefficient Q p i.val j.val :=
  pairCoefficient_eq Q p i j

private theorem radicand_factorization {Q p i j : ℕ} (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hw : i+j=p+1) :
    ((Q.descFactorial i:ℝ)*(Q.descFactorial j:ℝ)*(p.factorial:ℝ)) /
       ((Q:ℝ)*((2*Q-2).descFactorial p:ℝ)*(i.factorial:ℝ)*(j.factorial:ℝ)) =
      (scaledDescFactorial (2*Q) 2 p)⁻¹ * scaledDescFactorial Q 0 i *
        scaledDescFactorial Q 0 j *
        ((p.factorial:ℝ) / (2^p * i.factorial * j.factorial)) := by
  have hQR : (Q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ)
  have hd : ((2*Q-2).descFactorial p:ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.descFactorial_pos.mpr hp))
  have hi : (i.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hpow : (Q:ℝ)^i * (Q:ℝ)^j = (Q:ℝ) * (Q:ℝ)^p := by
    rw [← pow_add, hw, pow_succ']
  unfold scaledDescFactorial
  simp only [Nat.sub_zero, inv_div, Nat.cast_mul, Nat.cast_ofNat]
  symm
  calc
    _ = ((2*(Q:ℝ))^p * (Q.descFactorial i:ℝ) * (Q.descFactorial j:ℝ) * p.factorial) /
      (((2*Q-2).descFactorial p:ℝ) * ((Q:ℝ)^i * (Q:ℝ)^j) *
        (2^p * i.factorial * j.factorial)) := by
      field_simp
    _ = _ := by
      rw [hpow, mul_pow]
      field_simp

 

theorem sphericalPairCoefficient_factorization {Q p : ℕ} (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (i j : ℕ) :
    sphericalPairCoefficient Q p i j = pairScale Q p * modeScale Q i *
      modeScale Q j * limitPairCoefficient p i j := by
  unfold sphericalPairCoefficient limitPairCoefficient
  split_ifs with hw
  · have h1 := scaledDescFactorial_nonneg (2*Q) 2 p
    have h2 := scaledDescFactorial_nonneg Q 0 i
    have h3 := scaledDescFactorial_nonneg Q 0 j
    rw [radicand_factorization hQ hp hw]
    rw [Real.sqrt_mul (by positivity : 0 ≤
        (scaledDescFactorial (2*Q) 2 p)⁻¹ * scaledDescFactorial Q 0 i *
         scaledDescFactorial Q 0 j)]
    rw [Real.sqrt_mul (by positivity : 0 ≤
        (scaledDescFactorial (2*Q) 2 p)⁻¹ * scaledDescFactorial Q 0 i)]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (scaledDescFactorial (2*Q) 2 p)⁻¹)]
    unfold pairScale modeScale
    ring
  · simp

 
theorem sphericalPairCoefficient_tendsto (p i j : ℕ) :
    Tendsto (fun Q : ℕ => sphericalPairCoefficient Q p i j) atTop
      (𝓝 (limitPairCoefficient p i j)) := by
  have ht := (((pairScale_tendsto p).mul (modeScale_tendsto i)).mul
    (modeScale_tendsto j)).mul_const (limitPairCoefficient p i j)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (p+2)] with Q hQ
  exact (sphericalPairCoefficient_factorization (by omega) (by omega) i j).symm
end LaughlinFock
end

end OAI
