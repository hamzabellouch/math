import Mathlib
import OAI.Analysis.LaughlinFock.LadderCalculus

namespace OAI

/-! Scalar Action. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 

theorem gridInner_self_eq_zero {n m : ℕ} {f : GridVector}
    (hf : GridSupported n m f) (h : gridInner n m f f = 0) : f = 0 := by
  funext p q
  by_cases hp : p ≤ n
  · by_cases hq : q ≤ m
    · have hi : f p q * f p q ≤ gridInner n m f f := by
        apply le_trans (Finset.single_le_sum (fun a _ => mul_self_nonneg (f p a))
          (Finset.mem_range.mpr (by omega : q < m+1)))
        exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => mul_self_nonneg (f a b)))
          (Finset.mem_range.mpr (by omega : p < n+1))
      rw [h] at hi
      exact (mul_self_eq_zero.mp (le_antisymm hi (mul_self_nonneg (f p q))))
    · exact hf p q (Or.inr (by omega))
  · exact hf p q (Or.inl (by omega))

 

theorem coupledVector_lowest {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    gridLower n m (coupledVector n m z (n+m-2*z)) = 0 := by
  have hz : 2*z ≤ n+m := by omega
  let k := n+m-2*z
  have hLR : gridLower n m (gridRaise n m (coupledVector n m z k)) =
      spinStep k k ^ 2 • coupledVector n m z k := by
    rw [coupledVector_raise hn hm (by rfl : k ≤ n+m-2*z), gridLower_smul]
    change spinStep k k • gridLower n m (coupledVector n m z (k-1)) = _
    by_cases hk : k=0
    · simp [hk]
    · rw [coupledVector_lower hz (by dsimp [k] at *; omega),
        show k-1+1=k by omega, smul_smul, ← pow_two]
  have hsq : spinStep k k ^ 2 + (((n+m-2*z : ℕ) : ℝ)-2*k) = 0 := by
    rw [spinStep_sq (by omega : k ≤ k+1)]
    change (k:ℝ)*((k:ℝ)+1-k) + ((k:ℝ)-2*k) = 0
    ring
  have hRL := coupledVector_commutator hn hm k
  rw [hLR, ← add_smul, hsq, zero_smul] at hRL
  apply gridInner_self_eq_zero (gridLower_supported (coupledVector_supported hn hm k))
  rw [grid_adjoint, hRL, gridInner_zero_right]

 
theorem coupledVector_outside_ladder {n m z k : ℕ} (hz : 2*z ≤ n+m)
    (hk : n+m-2*z < k) : coupledVector n m z k = 0 := by
  have he : k=(k-1)+1 := by omega
  conv_lhs => rw [he, coupledVector_succ hz]
  rw [← he, spinStep_cutoff _ _ hk, inv_zero, zero_smul]

 

theorem coupledVector_lower_all {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (k : ℕ) :
    gridLower n m (coupledVector n m z k) =
      spinStep (n+m-2*z) (k+1) • coupledVector n m z (k+1) := by
  rcases lt_trichotomy k (n+m-2*z) with hk | rfl | hk
  · exact coupledVector_lower (by omega) hk
  · rw [coupledVector_lowest hn hm, spinStep_last, zero_smul]
  · rw [coupledVector_outside_ladder (by omega) hk,
      gridLower_zero, spinStep_cutoff _ _ (by omega), zero_smul]

 
theorem coupledVector_raise_all {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (k : ℕ) :
    gridRaise n m (coupledVector n m z k) =
      spinStep (n+m-2*z) k • coupledVector n m z (k-1) := by
  by_cases hk : k ≤ n+m-2*z
  · exact coupledVector_raise hn hm hk
  · rw [coupledVector_outside_ladder (by omega) (by omega),
      gridRaise_zero, spinStep_cutoff _ _ (by omega), zero_smul]

 

theorem grid_highest_eq_of_first {n m z : ℕ} (hz : z ≤ n) {f g : GridVector}
    (hf : GridLayer z f) (hg : GridLayer z g)
    (hRf : gridRaise n m f = 0) (hRg : gridRaise n m g = 0)
    (hfirst : f 0 z = g 0 z) : f = g := by
  have hc : ∀ p, p ≤ z → f p (z-p) = g p (z-p) := by
    intro p
    induction p with
    | zero => simpa using fun (_ : 0 ≤ z) => hfirst
    | succ p ih =>
      intro hp
      have heF := congrArg (fun h : GridVector => h p (z-(p+1))) hRf
      have heG := congrArg (fun h : GridVector => h p (z-(p+1))) hRg
      simp only [gridRaise, Pi.zero_apply,
        show z-(p+1)+1 = z-p by omega] at heF heG
      rw [ih (by omega)] at heF
      apply mul_left_cancel₀ (spinStep_pos (by omega : 0 < p+1) (by omega : p+1 ≤ n)).ne'
      linarith only [heF, heG]
  funext p q
  by_cases h : p+q=z
  · rw [show q=z-p by omega]
    exact hc p (by omega)
  · rw [hf p q h, hg p q h]

 

theorem highestCoefficient_first_ne_zero {n m z : ℕ} (hn : z ≤ n) :
    highestCoefficient n m z 0 ≠ 0 := by
  have hpos : 0 < highestCoefficient n m z 0 ^ 2 := by
    rw [highestCoefficient_sq]
    apply div_pos
    · simpa [highestWeight] using (show (0:ℝ) < n.descFactorial z by
        exact_mod_cast Nat.descFactorial_pos.mpr hn)
    · exact_mod_cast highestTotal_pos (m := m) hn
  exact fun h => by simp [h] at hpos

 

theorem grid_highest_unique {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m)
    {f : GridVector} (hf : GridLayer z f) (hRf : gridRaise n m f = 0) :
    f = (f 0 z / highestCoefficient n m z 0) • coupledVector n m z 0 := by
  apply grid_highest_eq_of_first (m := m) hn hf
  · intro p q hpq
    simp [coupledVector_layer n m z 0 p q (by simpa using hpq)]
  · exact hRf
  · rw [gridRaise_smul, coupledVector_highest hn hm, smul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul, coupledVector, zero_add, add_zero,
      ite_true, coupledCoefficient]
    exact (div_mul_cancel₀ _ (highestCoefficient_first_ne_zero hn)).symm

 

theorem coupledVector_intertwiner {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m)
    (A : GridVector →ₗ[ℝ] GridVector)
    (hL : ∀ f, A (gridLower n m f) = gridLower n m (A f))
    (hR : ∀ f, A (gridRaise n m f) = gridRaise n m (A f))
    (hLayer : ∀ T f, GridLayer T f → GridLayer T (A f)) (k : ℕ) :
    A (coupledVector n m z k) =
      (A (coupledVector n m z 0) 0 z / highestCoefficient n m z 0) •
        coupledVector n m z k := by
  induction k with
  | zero =>
    apply grid_highest_unique hn hm
    · exact hLayer z _ (by simpa using coupledVector_layer n m z 0)
    · rw [← hR, coupledVector_highest hn hm, map_zero]
  | succ k ih =>
    rw [coupledVector_succ (by omega : 2*z ≤ n+m), map_smul, hL, ih,
      gridLower_smul]
    exact smul_comm _ _ _

end LaughlinFock
end

end OAI
