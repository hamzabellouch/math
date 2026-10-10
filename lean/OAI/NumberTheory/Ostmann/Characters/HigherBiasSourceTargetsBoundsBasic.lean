import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTargetsAlgebra

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSourceTargets
open scoped BigOperators

def coefficient (J : ℝ) (a Δ : ℕ→ℝ) (j : ℕ) : ℝ := (2:ℝ)^j*J+a j-Δ (j+1)

def pivotTarget (k : ℕ) (J : ℝ) (a Δ : ℕ→ℝ) (j : ℕ) : ℝ :=
  target k (coefficient J a Δ) j

def fillerTarget (k : ℕ) (logX J : ℝ) (a Δ : ℕ→ℝ) : ℝ :=
  (logX+Δ 0)/2-J-∑j∈Finset.range k,(pivotTarget k J a Δ j+a j)

lemma coefficient_nonneg {k : ℕ} {τ J : ℝ} (hτ : 0≤τ)
    (hJ : (9/10:ℝ)*τ≤J) (a Δ : ℕ→ℝ)
    (ha : ∀j<k,0≤a j) (hΔ : ∀i≤k,Δ i≤τ/10) {j : ℕ} (hj : j<k) :
    0≤coefficient J a Δ j := by
  have hp : (1:ℝ)≤2^j := one_le_pow₀ (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hJ (by positivity : (0:ℝ)≤2^j)
  have hτp := mul_le_mul_of_nonneg_right hp hτ
  have haj := ha j hj
  have hd := hΔ (j+1) (by omega)
  unfold coefficient
  nlinarith

lemma coefficient_le {k : ℕ} {τ J : ℝ} (hτ : 0≤τ)
    (hJ : J≤4*τ) (a Δ : ℕ→ℝ)
    (ha : ∀j<k,a j≤4*τ) (hΔ : ∀i≤k,0≤Δ i) {j : ℕ} (hj : j<k) :
    coefficient J a Δ j≤8*(2:ℝ)^k*τ := by
  have hp : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  have hpow : (2:ℝ)^j≤2^k := pow_le_pow_right₀ (by norm_num) hj.le
  have hm := mul_le_mul_of_nonneg_left hJ (by positivity : (0:ℝ)≤2^j)
  have ht := mul_le_mul_of_nonneg_right hpow hτ
  have ht' := mul_le_mul_of_nonneg_right hp hτ
  have haj := ha j hj
  have hd := hΔ (j+1) (by omega)
  unfold coefficient
  nlinarith

lemma geometric_two_sum (k : ℕ) : ∑i∈Finset.range k,(2:ℝ)^i=2^k-1 := by
  have hh := geom_sum_mul (2:ℝ) k
  norm_num at hh
  exact hh

lemma two_pow_square (k : ℕ) : ((2:ℝ)^k)^2=(4:ℝ)^k := by
  rw [← pow_mul, mul_comm k 2,pow_mul]
  norm_num

lemma pivotTarget_total_le {k : ℕ} {τ J : ℝ} (hτ : 0≤τ)
    (hJ : J≤4*τ) (a Δ : ℕ→ℝ)
    (ha : ∀j<k,a j≤4*τ) (hΔ : ∀i≤k,0≤Δ i) :
    (∑j∈Finset.range k,pivotTarget k J a Δ j)≤8*(4:ℝ)^k*τ := by
  unfold pivotTarget
  rw [target_total]
  calc
    _ ≤ ∑j∈Finset.range k,(2:ℝ)^j*(8*(2:ℝ)^k*τ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (coefficient_le hτ hJ a Δ ha hΔ (Finset.mem_range.mp hj))
        (by positivity)
    _ = ((2:ℝ)^k-1)*(8*(2:ℝ)^k*τ) := by rw [← Finset.sum_mul,geometric_two_sum]
    _ ≤ (2:ℝ)^k*(8*(2:ℝ)^k*τ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 8*(4:ℝ)^k*τ := by rw [← two_pow_square];ring

lemma pivotTarget_lower {k j : ℕ} (hk : 0<k) (hj : j<k) {τ J : ℝ}
    (hτ : 0≤τ) (hJ : (9/10:ℝ)*τ≤J) (a Δ : ℕ→ℝ)
    (ha : ∀j<k,0≤a j) (hΔ : ∀i≤k,Δ i≤τ/10) :
    (1/10:ℝ)*(2:ℝ)^k*τ≤pivotTarget k J a Δ j := by
  have hc := fun i hi=>coefficient_nonneg hτ hJ a Δ ha hΔ (j:=i) hi
  apply le_trans _ (target_ge_last hj (coefficient J a Δ) hc)
  have hp : (1:ℝ)≤2^(k-1) := one_le_pow₀ (by norm_num)
  have he : (2:ℝ)^k=2*2^(k-1) := by
    conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ]
    ring
  have hm := mul_le_mul_of_nonneg_left hJ (by positivity : (0:ℝ)≤2^(k-1))
  have ht := mul_le_mul_of_nonneg_right hp hτ
  have haj := ha (k-1) (by omega)
  have hd := hΔ k (by omega)
  have hd' : Δ ((k-1)+1)≤τ/10 := by simpa [Nat.sub_add_cancel (show 1≤k by omega)] using hd
  unfold coefficient
  rw [he]
  nlinarith

lemma cast_le_four_pow (k : ℕ) : (k:ℝ)≤(4:ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.cast_succ,pow_succ]
    have hp : (1:ℝ)≤4^k := one_le_pow₀ (by norm_num)
    nlinarith

end Ostmann.Characters.HigherBiasSourceTargets

end

end OAI
