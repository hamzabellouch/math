import Mathlib

namespace OAI

/-! Scalar exponent inequalities for cubic-sieve recurrences. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.SieveScalar

lemma monomial {M d y : ℝ} (hM : 0<M) (hd : 0<d) (hy : 0<y) (p : ℝ) :
    (M/(d*y))*(d*y^2/M)^p = M^(1-p)*d^(p-1)*y^(2*p-1) := by
  rw [Real.div_rpow (by positivity) hM.le,Real.mul_rpow hd.le (sq_nonneg y),
    ← Real.rpow_natCast_mul hy.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_sub hM,Real.rpow_sub hd,Real.rpow_sub hy]
  simp only [Real.rpow_one]
  ring

lemma main_power {M N k d α : ℝ} (hM : 1≤M) (hN : 1≤N) (hk : 1≤k)
    (hkN : k≤N) (hd : 1≤d) (hdk : d≤k) (hα : 1≤α) :
    (M/(d*(N/k)))*(d*(N/k)^2/M)^α ≤ M^(1-α)*N^(2*α-1) := by
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hk0 : 0<k := by linarith
  have hd0 : 0<d := by linarith
  have hy1 : 1≤N/k := (le_div_iff₀ hk0).2 (by simpa using hkN)
  rw [monomial hM0 hd0 (lt_of_lt_of_le zero_lt_one hy1)]
  have hdα : d^(α-1) ≤ k^(2*α-1) := by
    calc
      _ ≤ k^(α-1) := Real.rpow_le_rpow hd0.le hdk (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk (by linarith)
  have he : k^(2*α-1)*(N/k)^(2*α-1) = N^(2*α-1) := by
    rw [← Real.mul_rpow hk0.le (div_pos hN0 hk0).le]
    congr 1
    field_simp
  calc
    _ ≤ M^(1-α)*k^(2*α-1)*(N/k)^(2*α-1) := by gcongr
    _ = _ := by rw [mul_assoc,he]

lemma mixed_one {M N k d : ℝ} (hM : 1≤M) (hN : 1≤N) (hk : 1≤k) (hd : 1≤d) :
    (M/(d*(N/k)))*(N/k)*(d*(N/k)^2/M)^(1/3:ℝ) ≤ (M*N)^(2/3:ℝ) := by
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hk0 : 0<k := by linarith
  have hd0 : 0<d := by linarith
  have hy : 0<N/k := div_pos hN0 hk0
  have hid : (M/(d*(N/k)))*(N/k)*(d*(N/k)^2/M)^(1/3:ℝ) = (M*(N/k)/d)^(2/3:ℝ) := by
    rw [mul_right_comm (M/(d*(N/k))) (N/k),monomial hM0 hd0 hy]
    rw [Real.div_rpow (by positivity) hd0.le,Real.mul_rpow hM0.le hy.le]
    norm_num
    have he : (N/k)^(-(1/3):ℝ)*(N/k) = (N/k)^(2/3:ℝ) := by
      calc
        _ = (N/k)^(-(1/3):ℝ)*(N/k)^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hy]; norm_num
    rw [mul_assoc,mul_assoc,he,Real.rpow_neg hd0.le]
    ring
  rw [hid]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  calc
    M*(N/k)/d ≤ M*(N/k) := div_le_self (by positivity) hd
    _ ≤ M*N := by gcongr; exact div_le_self hN0.le hk

lemma mixed_two {M N k d : ℝ} (hM : 1≤M) (hN : 1≤N) (hk : 1≤k) (hd : 1≤d) :
    (M/(d*(N/k)))*(N/k)^(2/3:ℝ)*(d*(N/k)^2/M)^(2/3:ℝ) ≤ M^(1/3:ℝ)*N := by
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hk0 : 0<k := by linarith
  have hd0 : 0<d := by linarith
  have hy : 0<N/k := div_pos hN0 hk0
  have hid : (M/(d*(N/k)))*(N/k)^(2/3:ℝ)*(d*(N/k)^2/M)^(2/3:ℝ) =
      M^(1/3:ℝ)*(N/k)/d^(1/3:ℝ) := by
    rw [mul_right_comm (M/(d*(N/k))) ((N/k)^(2/3:ℝ)),monomial hM0 hd0 hy]
    norm_num
    rw [mul_assoc,mul_assoc,← Real.rpow_add hy]
    norm_num
    rw [Real.rpow_neg hd0.le]
    ring
  rw [hid]
  calc
    _ ≤ M^(1/3:ℝ)*(N/k) := div_le_self (by positivity) (Real.one_le_rpow hd (by norm_num))
    _ ≤ _ := by gcongr; exact div_le_self hN0.le hk

lemma scale_epsilon {M N k d ε : ℝ} (hM : 1≤M) (hN : 1≤N) (hk : 1≤k)
    (hkN : k≤N) (hd : 1≤d) (hdk : d≤k) (hε : 0≤ε) :
    (N/k)^ε*(d*(N/k)^2/M)^ε ≤ N^(3*ε) := by
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hk0 : 0<k := by linarith
  have hd0 : 0<d := by linarith
  have hy1 : 1≤N/k := (le_div_iff₀ hk0).2 (by simpa using hkN)
  have hy : 0<N/k := lt_of_lt_of_le zero_lt_one hy1
  have hr := Real.rpow_natCast_mul hN0.le 3 ε
  norm_num only [Nat.cast_ofNat] at hr
  rw [← Real.mul_rpow hy.le (by positivity),hr]
  apply Real.rpow_le_rpow (by positivity) _ hε
  have hyN : N/k≤N := div_le_self hN0.le hk
  have hdY : d*(N/k)≤N := by
    calc
      _ ≤ k*(N/k) := by gcongr
      _ = N := by field_simp
  calc
    (N/k)*(d*(N/k)^2/M) ≤ (N/k)*(d*(N/k)^2) := by gcongr; exact div_le_self (by positivity) hM
    _ = (d*(N/k))*(N/k)^2 := by ring
    _ ≤ N*N^2 := by gcongr
    _ = N^3 := by ring

end CubicFirstMoment.SieveScalar
end

end OAI
