import Mathlib
import OAI.Analysis.LaughlinFock.FourCoefficients

namespace OAI

/-! Ladder Calculus. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 

def spinStep (n p : ℕ) : ℝ := Real.sqrt ((p : ℝ) * ((n : ℝ)+1-p))

@[simp] theorem spinStep_zero (n : ℕ) : spinStep n 0 = 0 := by simp [spinStep]

theorem spinStep_cutoff (n p : ℕ) (hp : n < p) : spinStep n p = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p)
  have h : (n : ℝ)+1 ≤ p := by exact_mod_cast hp
  linarith

@[simp] theorem spinStep_last (n : ℕ) : spinStep n (n+1) = 0 :=
  spinStep_cutoff n (n+1) (by omega)

theorem spinStep_sq {n p : ℕ} (hp : p ≤ n+1) :
    spinStep n p ^ 2 = (p : ℝ)*((n : ℝ)+1-p) := by
  apply Real.sq_sqrt
  apply mul_nonneg (Nat.cast_nonneg _)
  have h : (p : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hp
  linarith

theorem spinStep_sq_sub {n p : ℕ} (hp : p ≤ n) :
    spinStep n (p+1)^2 - spinStep n p^2 = (n : ℝ)-2*p := by
  rw [spinStep_sq (by omega : p+1 ≤ n+1), spinStep_sq (by omega : p ≤ n+1)]
  push_cast
  ring

theorem spinStep_pos {n p : ℕ} (hp0 : 0 < p) (hpn : p ≤ n) :
    0 < spinStep n p := by
  apply Real.sqrt_pos.mpr
  apply mul_pos (by exact_mod_cast hp0)
  have h : (p : ℝ) ≤ n := by exact_mod_cast hpn
  linarith

abbrev GridVector := ℕ → ℕ → ℝ

def GridSupported (n m : ℕ) (f : GridVector) : Prop :=
  ∀ p q, n < p ∨ m < q → f p q = 0

def GridLayer (T : ℕ) (f : GridVector) : Prop :=
  ∀ p q, p+q ≠ T → f p q = 0

 
def gridLower (n m : ℕ) (f : GridVector) : GridVector := fun p q =>
  spinStep n p * f (p-1) q + spinStep m q * f p (q-1)

 
def gridRaise (n m : ℕ) (f : GridVector) : GridVector := fun p q =>
  spinStep n (p+1) * f (p+1) q + spinStep m (q+1) * f p (q+1)

theorem gridLower_smul (n m : ℕ) (c : ℝ) (f : GridVector) :
    gridLower n m (c • f) = c • gridLower n m f := by
  funext p q
  simp only [gridLower, Pi.smul_apply, smul_eq_mul]
  ring

theorem gridRaise_smul (n m : ℕ) (c : ℝ) (f : GridVector) :
    gridRaise n m (c • f) = c • gridRaise n m f := by
  funext p q
  simp only [gridRaise, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem gridLower_zero (n m : ℕ) : gridLower n m 0 = 0 := by
  funext p q
  simp [gridLower]

@[simp] theorem gridRaise_zero (n m : ℕ) : gridRaise n m 0 = 0 := by
  funext p q
  simp [gridRaise]

theorem gridLower_supported {n m : ℕ} {f : GridVector} (hf : GridSupported n m f) :
    GridSupported n m (gridLower n m f) := by
  intro p q h
  rcases h with hp | hq
  · simp only [gridLower, spinStep_cutoff n p hp, zero_mul, zero_add,
      hf p (q-1) (Or.inl hp), mul_zero]
  · simp only [gridLower, spinStep_cutoff m q hq, mul_zero, zero_mul, add_zero,
      hf (p-1) q (Or.inr hq)]

theorem gridRaise_supported {n m : ℕ} {f : GridVector} (hf : GridSupported n m f) :
    GridSupported n m (gridRaise n m f) := by
  intro p q h
  have h1 : n < p+1 ∨ m < q := by omega
  have h2 : n < p ∨ m < q+1 := by omega
  simp [gridRaise, hf (p+1) q h1, hf p (q+1) h2]

theorem gridLower_layer {n m T : ℕ} {f : GridVector} (hf : GridLayer T f) :
    GridLayer (T+1) (gridLower n m f) := by
  intro p q h
  unfold gridLower
  have h1 : spinStep n p * f (p-1) q = 0 := by
    by_cases hp : p = 0
    · simp [hp]
    · rw [hf (p-1) q (by omega), mul_zero]
  have h2 : spinStep m q * f p (q-1) = 0 := by
    by_cases hq : q = 0
    · simp [hq]
    · rw [hf p (q-1) (by omega), mul_zero]
  rw [h1, h2, zero_add]

 

theorem grid_commutator_at (n m : ℕ) (f : GridVector) (p q : ℕ)
    (hp : p ≤ n) (hq : q ≤ m) :
    gridRaise n m (gridLower n m f) p q - gridLower n m (gridRaise n m f) p q =
      ((n : ℝ)+m-2*(p+q)) * f p q := by
  have hdiag : gridRaise n m (gridLower n m f) p q -
      gridLower n m (gridRaise n m f) p q =
      (spinStep n (p+1)^2-spinStep n p^2 +
        (spinStep m (q+1)^2-spinStep m q^2)) * f p q := by
    cases p <;> cases q <;>
      simp only [gridRaise, gridLower, Nat.succ_sub_one,
        spinStep_zero, zero_mul, zero_add, add_zero, zero_pow (by omega : 2 ≠ 0), sub_zero] <;> ring
  rw [hdiag, spinStep_sq_sub hp, spinStep_sq_sub hq]
  ring

 
theorem grid_commutator_layer {n m T : ℕ} {f : GridVector}
    (hf : GridSupported n m f) (hT : GridLayer T f) :
    gridRaise n m (gridLower n m f) = gridLower n m (gridRaise n m f) +
      ((n : ℝ)+m-2*T) • f := by
  funext p q
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : n < p ∨ m < q
  · rw [gridRaise_supported (gridLower_supported hf) p q h,
      gridLower_supported (gridRaise_supported hf) p q h, hf p q h]
    ring
  · have hp : p ≤ n := by omega
    have hq : q ≤ m := by omega
    have he := grid_commutator_at n m f p q hp hq
    by_cases hl : p+q = T
    · have hc : (p : ℝ) + q = T := by exact_mod_cast hl
      rw [hc] at he
      linarith only [he]
    · rw [hT p q hl, mul_zero] at he ⊢
      linarith

 
def gridInner (n m : ℕ) (f g : GridVector) : ℝ :=
  ∑ p ∈ Finset.range (n+1), ∑ q ∈ Finset.range (m+1), f p q * g p q

theorem gridInner_smul_left (n m : ℕ) (c : ℝ) (f g : GridVector) :
    gridInner n m (c • f) g = c * gridInner n m f g := by
  simp only [gridInner, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem gridInner_smul_right (n m : ℕ) (c : ℝ) (f g : GridVector) :
    gridInner n m f (c • g) = c * gridInner n m f g := by
  simp only [gridInner, Pi.smul_apply, smul_eq_mul, ←mul_assoc, mul_comm _ c, Finset.mul_sum]

theorem spinStep_sum_adjoint (n : ℕ) (f g : ℕ → ℝ) :
    (∑ p ∈ Finset.range (n+1), (spinStep n p * f (p-1)) * g p) =
      ∑ p ∈ Finset.range (n+1), f p * (spinStep n (p+1) * g (p+1)) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [spinStep_zero, zero_mul, spinStep_last, mul_zero, add_zero, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro p _
  ring

 

theorem grid_adjoint (n m : ℕ) (f g : GridVector) :
    gridInner n m (gridLower n m f) g = gridInner n m f (gridRaise n m g) := by
  simp only [gridInner, gridLower, gridRaise, add_mul, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_comm, Finset.sum_comm (f := fun p q => f p q * _)]
    apply Finset.sum_congr rfl
    intro q _
    exact spinStep_sum_adjoint n (fun p => f p q) (fun p => g p q)
  · apply Finset.sum_congr rfl
    intro p _
    exact spinStep_sum_adjoint m (f p) (g p)

 

def coupledVector (n m z k : ℕ) : GridVector := fun p q =>
  if p+q = z+k then coupledCoefficient n m z k p else 0

theorem coupledVector_layer (n m z k : ℕ) :
    GridLayer (z+k) (coupledVector n m z k) := by
  intro p q h
  exact ite_eq_right h

theorem coupledVector_supported {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (k : ℕ) :
    GridSupported n m (coupledVector n m z k) := by
  intro p q h
  unfold coupledVector
  split_ifs with he
  · rcases h with hp | hq
    · exact coupledCoefficient_left_support hn k p hp
    · exact coupledCoefficient_right_support hm k p (by omega)
  · rfl

theorem spinStep_succ {n p : ℕ} (hp : p ≤ n) :
    spinStep n (p+1) = Real.sqrt ((p+1 : ℕ) * (n-p : ℕ) : ℝ) := by
  unfold spinStep
  rw [Nat.cast_sub hp]
  congr 2
  push_cast
  ring

 

theorem coupledVector_highest {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    gridRaise n m (coupledVector n m z 0) = 0 := by
  funext p q
  simp only [gridRaise, coupledVector, Nat.add_zero, Pi.zero_apply]
  by_cases h : p+q+1 = z
  · have h1 : p+1+q = z := by omega
    have h2 : p+(q+1) = z := by omega
    rw [ite_eq_left h1, ite_eq_left h2, spinStep_succ (by omega : p ≤ n),
      spinStep_succ (by omega : q ≤ m)]
    have hq1 : q+1 = z-p := by omega
    have hmq : m-q = m-z+p+1 := by omega
    rw [hq1, hmq]
    simp only [coupledCoefficient]
    simpa only [mul_comm] using highestCoefficient_raising (m := m) hn (by omega : p < z)
  · rw [ite_eq_right (by omega : p+1+q ≠ z), ite_eq_right (by omega : p+(q+1) ≠ z)]
    ring

 

theorem coupledVector_succ_apply (n m z k p q : ℕ) :
    coupledVector n m z (k+1) p q = gridLower n m (coupledVector n m z k) p q /
      Real.sqrt (((k+1 : ℕ) : ℝ)*((n : ℝ)+m-2*z-k)) := by
  by_cases ht : p+q = z+k+1
  · have ht' : (p : ℝ)+q = (z : ℝ)+k+1 := by exact_mod_cast ht
    have hr1 : (((z+k+1 : ℕ) : ℝ)-p) = q := by push_cast; linarith
    have hr2 : (m : ℝ)+p-z-k = (m : ℝ)+1-q := by linarith
    simp only [coupledVector, show z+(k+1) = z+k+1 by omega, ht, ite_true,
      coupledCoefficient_lower, hr1, hr2, gridLower, spinStep,
      Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_mul (Nat.cast_nonneg q)]
    by_cases hp : p = 0
    · subst p
      have hq : 0+(q-1) = z+k := by omega
      simp [hq]
    · by_cases hq : q = 0
      · subst q
        have hp' : p-1+0 = z+k := by omega
        simp [hp']
      · rw [ite_eq_left (by omega : p-1+q = z+k), ite_eq_left (by omega : p+(q-1) = z+k)]
  · have hzero := gridLower_layer (n := n) (m := m) (coupledVector_layer n m z k) p q ht
    rw [hzero, zero_div]
    exact ite_eq_right (by omega)

theorem coupledVector_succ {n m z : ℕ} (hz : 2*z ≤ n+m) (k : ℕ) :
    coupledVector n m z (k+1) = (spinStep (n+m-2*z) (k+1))⁻¹ •
      gridLower n m (coupledVector n m z k) := by
  funext p q
  simp only [Pi.smul_apply, smul_eq_mul, coupledVector_succ_apply]
  have hden : Real.sqrt (((k+1 : ℕ) : ℝ)*((n : ℝ)+m-2*z-k)) =
      spinStep (n+m-2*z) (k+1) := by
    unfold spinStep
    rw [Nat.cast_sub hz]
    push_cast
    congr 2
    ring
  rw [hden, div_eq_mul_inv, mul_comm]

 

theorem coupledVector_lower {n m z k : ℕ} (hz : 2*z ≤ n+m)
    (hk : k < n+m-2*z) :
    gridLower n m (coupledVector n m z k) =
      spinStep (n+m-2*z) (k+1) • coupledVector n m z (k+1) := by
  have hpos := spinStep_pos (by omega : 0 < k+1) (by omega : k+1 ≤ n+m-2*z)
  rw [coupledVector_succ hz, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

 
theorem coupledVector_top_norm {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    gridInner n m (coupledVector n m z 0) (coupledVector n m z 0) = 1 := by
  have hq : ∀ p, (∑ q ∈ Finset.range (m+1),
      coupledVector n m z 0 p q * coupledVector n m z 0 p q) =
      if p ≤ z then highestCoefficient n m z p ^ 2 else 0 := by
    intro p
    by_cases hp : p ≤ z
    · rw [ite_eq_left hp]
      calc
        _ = coupledVector n m z 0 p (z-p) * coupledVector n m z 0 p (z-p) := by
          apply Finset.sum_eq_single (z-p)
          · intro q _ hne
            simp only [coupledVector, Nat.add_zero, ite_eq_right (by omega : p+q ≠ z), mul_zero]
          · intro hnot
            exact (hnot (Finset.mem_range.mpr (by omega : z-p < m+1))).elim
        _ = _ := by simp [coupledVector, coupledCoefficient, show p+(z-p) = z by omega, pow_two]
    · rw [ite_eq_right hp]
      apply Finset.sum_eq_zero
      intro q _
      simp only [coupledVector, Nat.add_zero, ite_eq_right (by omega : p+q ≠ z), mul_zero]
  simp only [gridInner, hq]
  calc
    _ = ∑ p ∈ Finset.range (z+1), if p ≤ z then highestCoefficient n m z p ^ 2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : z+1 ≤ n+1))
      intro p _ hout
      rw [Finset.mem_range] at hout
      exact ite_eq_right (by omega)
    _ = ∑ p ∈ Finset.range (z+1), highestCoefficient n m z p ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ite_eq_left (by have := Finset.mem_range.mp hp; omega)]
    _ = 1 := highestCoefficient_norm hn

 
theorem coupledVector_commutator {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (k : ℕ) :
    gridRaise n m (gridLower n m (coupledVector n m z k)) =
      gridLower n m (gridRaise n m (coupledVector n m z k)) +
        (((n+m-2*z : ℕ) : ℝ)-2*k) • coupledVector n m z k := by
  have h := grid_commutator_layer (coupledVector_supported hn hm k) (coupledVector_layer n m z k)
  convert h using 2
  rw [Nat.cast_sub (by omega : 2*z ≤ n+m)]
  push_cast
  ring_nf

 

theorem coupledVector_raise {n m z k : ℕ} (hn : z ≤ n) (hm : z ≤ m)
    (hk : k ≤ n+m-2*z) :
    gridRaise n m (coupledVector n m z k) =
      spinStep (n+m-2*z) k • coupledVector n m z (k-1) := by
  have hz : 2*z ≤ n+m := by omega
  revert hk
  induction k with
  | zero =>
    intro _
    simp only [coupledVector_highest hn hm, spinStep_zero, zero_smul]
  | succ k ih =>
    intro hk
    have hprev := ih (by omega : k ≤ n+m-2*z)
    have hLR : gridLower n m (gridRaise n m (coupledVector n m z k)) =
        spinStep (n+m-2*z) k ^ 2 • coupledVector n m z k := by
      rw [hprev, gridLower_smul]
      by_cases hk0 : k = 0
      · simp [hk0]
      · rw [coupledVector_lower hz (by omega : k-1 < n+m-2*z),
          show k-1+1 = k by omega, smul_smul, ← pow_two]
    have h := coupledVector_commutator hn hm k
    rw [coupledVector_lower hz (by omega : k < n+m-2*z), gridRaise_smul, hLR, ← add_smul] at h
    have hsq : spinStep (n+m-2*z) k ^ 2 + (((n+m-2*z : ℕ) : ℝ)-2*k) =
        spinStep (n+m-2*z) (k+1)^2 := by
      linarith only [spinStep_sq_sub (by omega : k ≤ n+m-2*z)]
    rw [hsq] at h
    have hpos := spinStep_pos (by omega : 0 < k+1) (by omega : k+1 ≤ n+m-2*z)
    funext p q
    have he := congrArg (fun f : GridVector => f p q) h
    simp only [Pi.smul_apply, smul_eq_mul] at he ⊢
    simp only [Nat.succ_sub_one]
    apply mul_left_cancel₀ hpos.ne'
    nlinarith only [he]

 

theorem coupledVector_norm {n m z k : ℕ} (hn : z ≤ n) (hm : z ≤ m)
    (hk : k ≤ n+m-2*z) :
    gridInner n m (coupledVector n m z k) (coupledVector n m z k) = 1 := by
  have hz : 2*z ≤ n+m := by omega
  revert hk
  induction k with
  | zero => exact fun _ => coupledVector_top_norm hn hm
  | succ k ih =>
    intro hk
    have hprev := ih (by omega : k ≤ n+m-2*z)
    have h := grid_adjoint n m (coupledVector n m z k) (coupledVector n m z (k+1))
    rw [coupledVector_lower hz (by omega : k < n+m-2*z),
      coupledVector_raise hn hm (by omega : k+1 ≤ n+m-2*z),
      Nat.add_sub_cancel, gridInner_smul_left, gridInner_smul_right, hprev, mul_one] at h
    have hpos := spinStep_pos (by omega : 0 < k+1) (by omega : k+1 ≤ n+m-2*z)
    apply mul_left_cancel₀ hpos.ne'
    simpa using h

@[simp] theorem gridInner_zero_right (n m : ℕ) (f : GridVector) :
    gridInner n m f 0 = 0 := by simp [gridInner]

@[simp] theorem gridInner_zero_left (n m : ℕ) (g : GridVector) :
    gridInner n m 0 g = 0 := by simp [gridInner]

theorem gridInner_comm (n m : ℕ) (f g : GridVector) :
    gridInner n m f g = gridInner n m g f := by
  simp only [gridInner, mul_comm]

theorem gridInner_of_layers {n m T U : ℕ} {f g : GridVector}
    (hf : GridLayer T f) (hg : GridLayer U g) (hTU : T ≠ U) :
    gridInner n m f g = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro q _
  by_cases h : p+q = T
  · rw [hg p q (by omega), mul_zero]
  · rw [hf p q h, zero_mul]

 

theorem coupledVector_orthogonal {n m z r k l : ℕ}
    (hzn : z ≤ n) (hzm : z ≤ m) (hrn : r ≤ n) (hrm : r ≤ m)
    (hzr : z < r) (hk : k ≤ n+m-2*z) (hl : l ≤ n+m-2*r) :
    gridInner n m (coupledVector n m z k) (coupledVector n m r l) = 0 := by
  have hz : 2*z ≤ n+m := by omega
  induction l generalizing k with
  | zero =>
    by_cases ht : z+k = r
    · have h := grid_adjoint n m (coupledVector n m z (k-1)) (coupledVector n m r 0)
      rw [coupledVector_lower hz (by omega : k-1 < n+m-2*z),
        show k-1+1 = k by omega, coupledVector_highest hrn hrm,
        gridInner_smul_left, gridInner_zero_right] at h
      exact (mul_eq_zero.mp h).resolve_left (spinStep_pos (by omega : 0 < k) hk).ne'
    · exact gridInner_of_layers (coupledVector_layer _ _ _ _) (coupledVector_layer _ _ _ _) (by omega)
  | succ l ih =>
    by_cases ht : z+k = r+(l+1)
    · have h := grid_adjoint n m (coupledVector n m z (k-1)) (coupledVector n m r (l+1))
      rw [coupledVector_lower hz (by omega : k-1 < n+m-2*z),
        show k-1+1 = k by omega,
        coupledVector_raise hrn hrm (by omega : l+1 ≤ n+m-2*r),
        Nat.add_sub_cancel, gridInner_smul_left, gridInner_smul_right,
        ih (by omega : k-1 ≤ n+m-2*z) (by omega : l ≤ n+m-2*r), mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (spinStep_pos (by omega : 0 < k) hk).ne'
    · exact gridInner_of_layers (coupledVector_layer _ _ _ _) (coupledVector_layer _ _ _ _) (by omega)

 

theorem coupledVector_gram {n m z r k l : ℕ}
    (hzn : z ≤ n) (hzm : z ≤ m) (hrn : r ≤ n) (hrm : r ≤ m)
    (hk : k ≤ n+m-2*z) (hl : l ≤ n+m-2*r) :
    gridInner n m (coupledVector n m z k) (coupledVector n m r l) =
      if z = r ∧ k = l then 1 else 0 := by
  rcases lt_trichotomy z r with hzr | rfl | hrz
  · rw [ite_eq_right (by omega)]
    exact coupledVector_orthogonal hzn hzm hrn hrm hzr hk hl
  · by_cases hkl : k = l
    · subst l
      rw [ite_eq_left ⟨rfl, rfl⟩]
      exact coupledVector_norm hzn hzm hk
    · rw [ite_eq_right (by tauto)]
      exact gridInner_of_layers (coupledVector_layer _ _ _ _) (coupledVector_layer _ _ _ _) (by omega)
  · rw [ite_eq_right (by omega), gridInner_comm]
    exact coupledVector_orthogonal hrn hrm hzn hzm hrz hl hk

end LaughlinFock
end

end OAI
