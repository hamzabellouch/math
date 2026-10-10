import Mathlib

namespace OAI

noncomputable section

namespace Problem315
namespace DisjointIndicators

def normalizedFlag {E : Type*} [AddCommGroup E] [Module ℝ E]
    (e A : E) (p : ℝ) : E :=
  (Real.sqrt (p * (1 - p)))⁻¹ • (A - p • e)

def correlation (p q : ℝ) : ℝ :=
  -(p * q) / (Real.sqrt (p * (1 - p)) * Real.sqrt (q * (1 - q)))

theorem correlation_sq_lt_one (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hsum : p + q < 1) : correlation p q ^ 2 < 1 := by
  have hp1 : p < 1 := by linarith
  have hq1 : q < 1 := by linarith
  have hpvar : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hqvar : 0 < q * (1 - q) := mul_pos hq (sub_pos.mpr hq1)
  have hden : 0 < Real.sqrt (p * (1 - p)) * Real.sqrt (q * (1 - q)) :=
    mul_pos (Real.sqrt_pos.2 hpvar) (Real.sqrt_pos.2 hqvar)
  unfold correlation
  rw [div_pow]
  apply (div_lt_one (sq_pos_of_pos hden)).2
  rw [mul_pow, Real.sq_sqrt hpvar.le, Real.sq_sqrt hqvar.le]
  have hslack : 0 < p * q * (1 - p - q) :=
    mul_pos (mul_pos hp hq) (by linarith)
  nlinarith

theorem correlation_nondegenerate (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hsum : p + q < 1) : 1 - correlation p q ^ 2 ≠ 0 :=
  ne_of_gt (sub_pos.mpr (correlation_sq_lt_one p q hp hq hsum))

theorem centered_inner_self
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e A : E) (p : ℝ) (hee : inner ℝ e e = 1)
    (hAe : inner ℝ A e = p) (hAA : inner ℝ A A = p) :
    inner ℝ (A - p • e) (A - p • e) = p * (1 - p) := by
  have heA : inner ℝ e A = p := by rw [real_inner_comm, hAe]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hee, hAe, heA, hAA]
  ring

theorem centered_cross_inner
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e A B : E) (p q : ℝ) (hee : inner ℝ e e = 1)
    (hAe : inner ℝ A e = p) (hBe : inner ℝ B e = q)
    (hAB : inner ℝ A B = 0) :
    inner ℝ (A - p • e) (B - q • e) = -(p * q) := by
  have heB : inner ℝ e B = q := by rw [real_inner_comm, hBe]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hee, hAe, heB, hAB]
  ring

theorem normalizedFlag_inner_self
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e A : E) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hee : inner ℝ e e = 1) (hAe : inner ℝ A e = p) (hAA : inner ℝ A A = p) :
    inner ℝ (normalizedFlag e A p) (normalizedFlag e A p) = 1 := by
  have hpvar : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1 - p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpvar)
  unfold normalizedFlag
  rw [real_inner_smul_left, real_inner_smul_right, centered_inner_self e A p hee hAe hAA]
  field_simp
  nlinarith [Real.sq_sqrt hpvar.le]

theorem normalizedFlag_cross_inner
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e A B : E) (p q : ℝ) (hee : inner ℝ e e = 1)
    (hAe : inner ℝ A e = p) (hBe : inner ℝ B e = q)
    (hAB : inner ℝ A B = 0) :
    inner ℝ (normalizedFlag e A p) (normalizedFlag e B q) = correlation p q := by
  unfold normalizedFlag correlation
  rw [real_inner_smul_left, real_inner_smul_right, centered_cross_inner e A B p q hee hAe hBe hAB]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem normalized_flags_gram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e A B : E) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hsum : p + q < 1)
    (hee : inner ℝ e e = 1)
    (hAe : inner ℝ A e = p) (hAA : inner ℝ A A = p)
    (hBe : inner ℝ B e = q) (hBB : inner ℝ B B = q)
    (hAB : inner ℝ A B = 0) :
    inner ℝ (normalizedFlag e A p) (normalizedFlag e A p) = 1 ∧
    inner ℝ (normalizedFlag e B q) (normalizedFlag e B q) = 1 ∧
    inner ℝ (normalizedFlag e A p) (normalizedFlag e B q) = correlation p q ∧
    1 - correlation p q ^ 2 ≠ 0 := by
  exact ⟨normalizedFlag_inner_self e A p hp (by linarith) hee hAe hAA,
    normalizedFlag_inner_self e B q hq (by linarith) hee hBe hBB,
    normalizedFlag_cross_inner e A B p q hee hAe hBe hAB,
    correlation_nondegenerate p q hp hq hsum⟩

theorem normalizedFlag_centered
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e A : E) (p : ℝ) (hee : inner ℝ e e = 1) (hAe : inner ℝ A e = p) :
    inner ℝ (normalizedFlag e A p) e = 0 := by
  simp only [normalizedFlag, real_inner_smul_left, inner_sub_left,
    hee, hAe, mul_one, sub_self, mul_zero]

theorem normalizedFlag_fixed
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : E →ₗ[ℝ] E) (e A : E) (p : ℝ) (he : P e = e) (hA : P A = A) :
    P (normalizedFlag e A p) = normalizedFlag e A p := by
  simp only [normalizedFlag, map_smul, map_sub, he, hA]

end DisjointIndicators
end Problem315

end

end OAI
