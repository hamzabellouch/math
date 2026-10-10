import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter

namespace OrdinaryCorrelations.Completion
open ArithmeticFunction Finset

lemma one_or_zero {f : ℕ → ℂ} (hf : Multiplicative f) :
    f 1 = 1 ∨ ∀ n, 0 < n → f n = 0 := by
  have he : f 1 * f 1 = f 1 := by
    simpa using (hf 1 1 (by omega) (by omega) (by simp)).symm
  have hz : f 1 * (f 1 - 1) = 0 := by rw [mul_sub,mul_one,he,sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · right
    intro n hn
    simpa [h] using hf 1 n (by omega) hn (by simp)
  · exact Or.inl (sub_eq_zero.mp h)

def arithmetic (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

@[simp] lemma arithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    arithmetic f n = f n := by simp [arithmetic,hn]

lemma arithmetic_multiplicative {f : ℕ → ℂ} (hf : Multiplicative f) (h1 : f 1 = 1) :
    (arithmetic f).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simpa using h1, ?_⟩
  intro m n hm hn hmn
  simpa [arithmetic_apply_pos,hm,hn,mul_ne_zero hm hn] using
    hf m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn

def complete (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n.primeFactorsList.map f).prod, by simp⟩

@[simp] lemma complete_one (f : ℕ → ℂ) : complete f 1 = 1 := by simp [complete]

lemma complete_mul (f : ℕ → ℂ) (m n : ℕ) :
    complete f (m*n) = complete f m * complete f n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [complete, ArithmeticFunction.coe_mk, ite_eq_right hm, ite_eq_right hn,
    ite_eq_right (mul_ne_zero hm hn)]
  rw [((Nat.perm_primeFactorsList_mul hm hn).map f).prod_eq]
  simp

lemma complete_multiplicative (f : ℕ → ℂ) : (complete f).IsMultiplicative :=
  ⟨complete_one f, fun {_ _} _ => complete_mul f _ _⟩

@[simp] lemma complete_prime (f : ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    complete f p = f p := by simp [complete,hp.ne_zero,Nat.primeFactorsList_prime hp]

lemma complete_pow (f : ℕ → ℂ) (n k : ℕ) : complete f (n^k) = complete f n ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, complete_mul, ih, pow_succ]

lemma complete_oneBounded {f : ℕ → ℂ} (hf : OneBounded f) : OneBounded (complete f) := by
  intro n
  by_cases hn : n = 0
  · simp [hn]
  simp only [complete, ArithmeticFunction.coe_mk, ite_eq_right hn]
  have hl (l : List ℕ) : ‖(l.map f).prod‖ ≤ 1 := by
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons,List.prod_cons,norm_mul]
      exact (mul_le_mul_of_nonneg_right (hf p) (norm_nonneg _)).trans (by simpa using ih)
  exact hl _

lemma complete_pmul_convolution (f : ℕ → ℂ) (a b : ArithmeticFunction ℂ) :
    (complete f).pmul (a*b) = (complete f).pmul a * (complete f).pmul b := by
  ext n
  simp only [pmul_apply,mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hm : d.1*d.2 = n := (Nat.mem_divisorsAntidiagonal.mp hd).1
  rw [← hm,complete_mul]
  ring

lemma complete_pmul_one (f : ℕ → ℂ) : (complete f).pmul 1 = 1 := by
  ext n
  by_cases hn : n = 1
  · simp [hn]
  · simp [ArithmeticFunction.one_apply_ne hn]

def completeInverse (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  (complete f).pmul (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

lemma completeInverse_mul (f : ℕ → ℂ) : completeInverse f * complete f = 1 := by
  have he := complete_pmul_convolution f (ArithmeticFunction.moebius : ArithmeticFunction ℂ)
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ)
  simpa [completeInverse,coe_moebius_mul_coe_zeta,complete_pmul_one] using he.symm

def kernel (f : ℕ → ℂ) : ArithmeticFunction ℂ := arithmetic f * completeInverse f

lemma kernel_reconstruct (f : ℕ → ℂ) : kernel f * complete f = arithmetic f := by
  rw [kernel,mul_assoc,completeInverse_mul,mul_one]

lemma kernel_multiplicative {f : ℕ → ℂ} (hf : Multiplicative f) (h1 : f 1 = 1) :
    (kernel f).IsMultiplicative :=
  (arithmetic_multiplicative hf h1).mul
    ((complete_multiplicative f).pmul ArithmeticFunction.isMultiplicative_moebius.intCast)

lemma complete_distanceSq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    distanceSq (complete f) χ t X = distanceSq f χ t X := by
  unfold distanceSq
  apply Finset.sum_congr rfl
  intro p hp
  rw [complete_prime f (Finset.mem_filter.mp hp).2]

lemma complete_uniformlyNonpretentious {f : ℕ → ℂ} (hf : UniformlyNonpretentious f) :
    UniformlyNonpretentious (complete f) := by
  simpa only [UniformlyNonpretentious,distance,complete_distanceSq] using hf

end OrdinaryCorrelations.Completion

end

end OAI
