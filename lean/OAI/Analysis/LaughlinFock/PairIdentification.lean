import Mathlib
import OAI.Analysis.LaughlinFock.LadderCalculus

namespace OAI

/-! Pair Identification. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 

theorem spinStep_mul_choose (n p : ℕ) :
    spinStep n p * Real.sqrt (n.choose (p-1) : ℝ) =
      (p : ℝ) * Real.sqrt (n.choose p : ℝ) := by
  rcases p with _ | p
  · simp
  by_cases hp : p+1 ≤ n
  · have hc : ((n.choose (p+1) : ℝ)) * (p+1 : ℕ) =
        ((n.choose p : ℝ)) * (n-p : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq n p
    apply (sq_eq_sq₀ (by unfold spinStep; positivity : 0 ≤ spinStep n (p+1) * Real.sqrt (n.choose ((p+1)-1) : ℝ))
      (by positivity : 0 ≤ ((p+1 : ℕ) : ℝ)*Real.sqrt (n.choose (p+1) : ℝ))).mp
    rw [mul_pow, mul_pow, spinStep_sq (by omega), Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    simp only [Nat.add_sub_cancel]
    rw [Nat.cast_sub (by omega : p ≤ n)] at hc
    push_cast at hc ⊢
    have h := congrArg (fun x : ℝ => ((p:ℝ)+1)*x) hc
    nlinarith only [h]
  · rw [spinStep_cutoff n (p+1) (by omega), Nat.choose_eq_zero_of_lt (by omega : n < p+1)]
    simp

 

def rawPairGrid (Q p : ℕ) : GridVector := fun i j =>
  if i+j=p+1 then
    ((i:ℝ)-j) * Real.sqrt (Q.choose i : ℝ) * Real.sqrt (Q.choose j : ℝ)
  else 0

theorem rawPairGrid_layer (Q p : ℕ) : GridLayer (p+1) (rawPairGrid Q p) := by
  intro i j hij
  exact ite_eq_right hij

 

theorem rawPairGrid_lower (Q p : ℕ) :
    gridLower Q Q (rawPairGrid Q p) = ((p+1 : ℕ) : ℝ) • rawPairGrid Q (p+1) := by
  funext i j
  by_cases ht : i+j=p+2
  · change spinStep Q i * rawPairGrid Q p (i-1) j +
      spinStep Q j * rawPairGrid Q p i (j-1) =
        ((p+1 : ℕ) : ℝ) * rawPairGrid Q (p+1) i j
    conv_rhs => rw [rawPairGrid, ite_eq_left (by omega : i+j=p+1+1)]
    have ht' : (i:ℝ)+j = (p:ℝ)+2 := by exact_mod_cast ht
    by_cases hi : i=0
    · subst i
      simp only [spinStep_zero, zero_mul, zero_add, rawPairGrid,
        ite_eq_left (by omega : (j-1)=p+1), Nat.cast_zero, zero_sub, Nat.choose_zero_right,
        Nat.cast_one, Real.sqrt_one, mul_one]
      rw [show spinStep Q j * (-((j-1:ℕ):ℝ) * Real.sqrt (Q.choose (j-1) : ℝ)) =
        -((j-1:ℕ):ℝ) * (spinStep Q j * Real.sqrt (Q.choose (j-1) : ℝ)) by ring,
        spinStep_mul_choose]
      rw [Nat.cast_sub (by omega : 1 ≤ j)]
      push_cast
      have he : (j:ℝ)=(p:ℝ)+2 := by exact_mod_cast (show j=p+2 by omega)
      rw [he]
      ring
    · by_cases hj : j=0
      · subst j
        simp only [spinStep_zero, zero_mul, add_zero, rawPairGrid,
          ite_eq_left (by omega : i-1=p+1), Nat.cast_zero, sub_zero,
          Nat.choose_zero_right, Nat.cast_one, Real.sqrt_one, mul_one]
        rw [show spinStep Q i * (((i-1:ℕ):ℝ) * Real.sqrt (Q.choose (i-1) : ℝ)) =
          ((i-1:ℕ):ℝ) * (spinStep Q i * Real.sqrt (Q.choose (i-1) : ℝ)) by ring,
          spinStep_mul_choose]
        rw [Nat.cast_sub (by omega : 1 ≤ i)]
        push_cast
        have he : (i:ℝ)=(p:ℝ)+2 := by exact_mod_cast (show i=p+2 by omega)
        rw [he]
        ring
      · simp only [rawPairGrid, ite_eq_left (by omega : i-1+j=p+1),
          ite_eq_left (by omega : i+(j-1)=p+1)]
        rw [show spinStep Q i * ((((i-1:ℕ):ℝ)-j) *
            Real.sqrt (Q.choose (i-1) : ℝ) * Real.sqrt (Q.choose j : ℝ)) =
          (((i-1:ℕ):ℝ)-j) * (spinStep Q i * Real.sqrt (Q.choose (i-1) : ℝ)) *
            Real.sqrt (Q.choose j : ℝ) by ring,
          show spinStep Q j * (((i:ℝ)-(j-1:ℕ)) *
            Real.sqrt (Q.choose i : ℝ) * Real.sqrt (Q.choose (j-1) : ℝ)) =
          ((i:ℝ)-(j-1:ℕ)) * Real.sqrt (Q.choose i : ℝ) *
            (spinStep Q j * Real.sqrt (Q.choose (j-1) : ℝ)) by ring,
          spinStep_mul_choose, spinStep_mul_choose,
          Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_sub (by omega : 1 ≤ j)]
        push_cast
        have he : (p:ℝ)+1=(i:ℝ)+j-1 := by linarith
        rw [he]
        ring
  · have h := gridLower_layer (n := Q) (m := Q) (rawPairGrid_layer Q p) i j (by omega)
    simp only [h, Pi.smul_apply, smul_eq_mul, rawPairGrid,
      ite_eq_right (by omega : i+j≠p+1+1), mul_zero]

 
def pairTensorNormalizer (Q p : ℕ) : ℝ :=
  Real.sqrt (2*(Q:ℝ)*((2*Q-2).choose p : ℝ))

theorem pairTensorNormalizer_pos {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    0 < pairTensorNormalizer Q p := by
  unfold pairTensorNormalizer
  apply Real.sqrt_pos.mpr
  have hq : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hc : 0 < ((2*Q-2).choose p : ℝ) := by exact_mod_cast Nat.choose_pos hp
  positivity

theorem pairTensorNormalizer_recurrence {Q p : ℕ} (hp : p < 2*Q-2) :
    spinStep (2*Q-2) (p+1) * pairTensorNormalizer Q p =
      ((p+1 : ℕ):ℝ) * pairTensorNormalizer Q (p+1) := by
  apply (sq_eq_sq₀ (by unfold spinStep pairTensorNormalizer; positivity)
    (by unfold pairTensorNormalizer; positivity)).mp
  rw [mul_pow, mul_pow, spinStep_sq (by omega)]
  rw [pairTensorNormalizer, pairTensorNormalizer,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hc : (((2*Q-2).choose (p+1) : ℝ)) * (p+1 : ℕ) =
      (((2*Q-2).choose p : ℝ)) * ((2*Q-2)-p : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq (2*Q-2) p
  rw [Nat.cast_sub (by omega : p ≤ 2*Q-2)] at hc
  have h := congrArg (fun x : ℝ => 2*(Q:ℝ)*((p+1:ℕ):ℝ)*x) hc
  push_cast at h ⊢
  nlinarith only [h]

 
def normalizedPairGrid (Q p : ℕ) : GridVector :=
  (pairTensorNormalizer Q p)⁻¹ • rawPairGrid Q p

theorem normalizedPairGrid_succ {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p < 2*Q-2) :
    normalizedPairGrid Q (p+1) = (spinStep (2*Q-2) (p+1))⁻¹ •
      gridLower Q Q (normalizedPairGrid Q p) := by
  rw [normalizedPairGrid, normalizedPairGrid, gridLower_smul,
    rawPairGrid_lower, smul_smul, smul_smul]
  have h1 := (pairTensorNormalizer_pos hQ (by omega : p ≤ 2*Q-2)).ne'
  have h2 := (pairTensorNormalizer_pos hQ (by omega : p+1 ≤ 2*Q-2)).ne'
  have h3 := (spinStep_pos (by omega : 0 < p+1) (by omega : p+1 ≤ 2*Q-2)).ne'
  congr 1
  field_simp [h1, h2, h3]
  simpa only [mul_comm] using pairTensorNormalizer_recurrence hp

 
theorem normalizedPairGrid_top {Q : ℕ} (hQ : 1 ≤ Q) :
    normalizedPairGrid Q 0 = coupledVector Q Q 1 0 := by
  have hpred : Q-1+1 = Q := by omega
  have htotal : highestTotal Q Q 1 = 2*Q := by
    simp [highestTotal, Finset.sum_range_succ, highestWeight, hpred, two_mul]
  funext i j
  by_cases ht : i+j=1
  · have hcases : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by omega
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals
      simp [normalizedPairGrid, rawPairGrid, pairTensorNormalizer, coupledVector,
        coupledCoefficient, highestCoefficient, highestWeight, htotal, hpred,
        Real.sqrt_div (Nat.cast_nonneg Q)]
      ring
  · simp [normalizedPairGrid, rawPairGrid, coupledVector, ht]

 

theorem normalizedPairGrid_eq_coupled {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    normalizedPairGrid Q p = coupledVector Q Q 1 p := by
  induction p with
  | zero => exact normalizedPairGrid_top hQ
  | succ p ih =>
    rw [normalizedPairGrid_succ hQ (by omega), ih (by omega),
      coupledVector_succ (by omega : 2*1 ≤ Q+Q)]
    simp only [two_mul, mul_one]

 

theorem sphericalPairCoefficient_eq_normalized {Q p : ℕ} (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) (i j : ℕ) :
    sphericalPairCoefficient Q p i j = Real.sqrt 2 * normalizedPairGrid Q p i j := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hp).ne'
  have hi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hf : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hr : ((Q.descFactorial i : ℝ)*(Q.descFactorial j : ℝ)*(p.factorial : ℝ)) /
      ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(i.factorial : ℝ)*(j.factorial : ℝ)) =
      ((Q.choose i : ℝ)*(Q.choose j : ℝ)) / ((Q : ℝ)*((2*Q-2).choose p : ℝ)) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold sphericalPairCoefficient normalizedPairGrid rawPairGrid
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs with hw
  · rw [hr, Real.sqrt_div (by positivity),
      Real.sqrt_mul (Nat.cast_nonneg (Q.choose i))]
    unfold pairTensorNormalizer
    rw [mul_assoc (2 : ℝ), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    field_simp
  · simp

 

theorem pairCoefficient_eq_coupled {Q p : ℕ} (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) (i j : Orbital Q) :
    pairCoefficient Q p i j = Real.sqrt 2 * coupledVector Q Q 1 p i j := by
  rw [pairCoefficient_eq_sphericalPairCoefficient,
    sphericalPairCoefficient_eq_normalized hQ hp, normalizedPairGrid_eq_coupled hQ hp]

end LaughlinFock
end

end OAI
