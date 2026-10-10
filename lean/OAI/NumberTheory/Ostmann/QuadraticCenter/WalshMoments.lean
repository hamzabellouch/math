import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_false : sign false = 1 := rfl
@[simp] theorem sign_true : sign true = -1 := rfl

def signMonomial {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (ε : ι → Bool) : ℝ :=
  ∏ i, sign (ε i) ^ e i

noncomputable def signMean {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ ε, f ε

@[simp] theorem sign_pow_sum (n : ℕ) :
    (∑ b : Bool, sign b ^ n) = if Even n then 2 else 0 := by
  simp only [Fintype.sum_bool, sign_false, sign_true, one_pow]
  split_ifs with h
  · rw [h.neg_one_pow]
    norm_num
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]
    norm_num

theorem signMonomial_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) :
    (∑ ε : ι → Bool, signMonomial e ε) =
      if ∀ i, Even (e i) then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  have hprod : (∑ ε : ι → Bool, signMonomial e ε) =
      ∏ i, ∑ b : Bool, sign b ^ e i := by
    simpa only [signMonomial, Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (ι := ι) (Finset.univ : Finset Bool)
        (fun i b => sign b ^ e i))
  rw [hprod]
  simp_rw [sign_pow_sum]
  split_ifs with h
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem signMonomial_mean {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) :
    signMean (signMonomial e) = if ∀ i, Even (e i) then 1 else 0 := by
  classical
  rw [signMean, signMonomial_sum]
  split_ifs with h
  · simp
  · simp

theorem signMonomial_add {ι : Type*} [Fintype ι] [DecidableEq ι] (e f : ι → ℕ)
    (ε : ι → Bool) :
    signMonomial (e + f) ε = signMonomial e ε * signMonomial f ε := by
  simp only [signMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem signMonomial_sum_exponents {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (e : α → ι → ℕ) (ε : ι → Bool) :
    signMonomial (∑ a, e a) ε = ∏ a, signMonomial (e a) ε := by
  simp only [signMonomial, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_comm

theorem signMean_power_sum {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (e : α → ι → ℕ) (c : α → ℝ) (n : ℕ) :
    signMean (fun ε => (∑ a, c a * signMonomial (e a) ε) ^ n) =
      ∑ f : Fin n → α, (∏ j, c (f j)) *
        (if ∀ i, Even (∑ j, e (f j) i) then 1 else 0) := by
  classical
  have hexp (ε : ι → Bool) :
      (∑ a, c a * signMonomial (e a) ε) ^ n =
        ∑ f : Fin n → α, (∏ j, c (f j)) *
          signMonomial (∑ j, e (f j)) ε := by
    calc
      _ = ∑ f : Fin n → α, ∏ j, c (f j) * signMonomial (e (f j)) ε := by
        simpa only [Fintype.piFinset_univ] using
          Finset.sum_pow' Finset.univ (fun a => c a * signMonomial (e a) ε) n
      _ = _ := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [Finset.prod_mul_distrib, signMonomial_sum_exponents]
  simp_rw [hexp]
  rw [signMean, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← Finset.mul_sum]
  rw [← mul_assoc, mul_comm _ (∏ j, c (f j)), mul_assoc]
  congr 1
  simpa only [signMean, Finset.sum_apply] using
    signMonomial_mean (∑ j : Fin n, e (f j))

theorem signMean_const_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (f : (ι → Bool) → ℝ) :
    signMean (fun ε => c * f ε) = c * signMean f := by
  simp only [signMean, ← Finset.mul_sum]
  ring

theorem signMean_sum {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (f : α → (ι → Bool) → ℝ) :
    signMean (fun ε => ∑ a, f a ε) = ∑ a, signMean (f a) := by
  simp only [signMean, Finset.mul_sum]
  exact Finset.sum_comm

def walshCharacter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (ε : ι → Bool) : ℝ :=
  signMonomial (fun i => if i ∈ s then 1 else 0) ε

theorem walshCharacter_orthogonality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : Finset ι) :
    signMean (fun ε => walshCharacter s ε * walshCharacter t ε) =
      if s = t then 1 else 0 := by
  classical
  simp only [walshCharacter, ← signMonomial_add]
  rw [signMonomial_mean]
  have h : (∀ i, Even ((if i ∈ s then 1 else 0) + (if i ∈ t then 1 else 0) : ℕ)) ↔
      s = t := by
    constructor
    · intro he
      ext i
      specialize he i
      by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
    · rintro rfl i
      by_cases hi : i ∈ s <;> simp [hi]
  simp only [Pi.add_apply, h]

theorem walsh_sum_sq_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) :
    signMean (fun ε => (∑ s : Finset ι, c s * walshCharacter s ε) ^ 2) =
      ∑ s : Finset ι, (c s) ^ 2 := by
  classical
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [signMean_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [signMean_sum]
  have hx (t : Finset ι) :
      signMean (fun ε => c t * walshCharacter t ε * (c s * walshCharacter s ε)) =
        c t * c s * (if t = s then 1 else 0) := by
    have hm (ε : ι → Bool) :
        c t * walshCharacter t ε * (c s * walshCharacter s ε) =
          (c t * c s) * (walshCharacter t ε * walshCharacter s ε) := by ring
    simp_rw [hm]
    rw [signMean_const_mul, walshCharacter_orthogonality]
  simp_rw [hx]
  simp

end Ostmann.QuadraticCenter

end OAI
