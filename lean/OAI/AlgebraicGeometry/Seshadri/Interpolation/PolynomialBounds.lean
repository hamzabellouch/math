import Mathlib

namespace OAI


                                          
section

namespace MaximalSeshadri.NefNumerics
lemma quadratic_nonpos_leading (a b c : ℤ)
    (h : ∀ n : ℕ, a*(n:ℤ)^2+b*n+c ≤ 0) : a ≤ 0 := by
  by_contra hn
  have ha : 1 ≤ a := by omega
  let n := (2*|b|+2*|c|+3).toNat
  have he : (n:ℤ) = 2*|b|+2*|c|+3 := Int.toNat_of_nonneg (by positivity)
  have hp : 0 ≤ (n:ℤ) := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_right ha (sq_nonneg (n:ℤ))
  have hb := mul_le_mul_of_nonneg_right (neg_abs_le b) hp
  have hc := neg_abs_le c
  have H := h n
  have hab := abs_nonneg b
  have hac := abs_nonneg c
  nlinarith

lemma linear_nonpos_leading (a c : ℤ)
    (h : ∀ n : ℕ, a*(n:ℤ)+c ≤ 0) : a ≤ 0 := by
  by_contra hn
  have ha : 1 ≤ a := by omega
  let n := (|c|+1).toNat
  have he : (n:ℤ) = |c|+1 := Int.toNat_of_nonneg (by positivity)
  have hm := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n : (0:ℤ) ≤ n)
  have hc := neg_abs_le c
  have H := h n
  nlinarith [abs_nonneg c]

lemma quadratic_bounded (a b c lo hi : ℤ)
    (h : ∀ n : ℕ, lo ≤ a*(n:ℤ)^2+b*n+c ∧ a*(n:ℤ)^2+b*n+c ≤ hi) :
    a = 0 ∧ b = 0 ∧ lo ≤ c ∧ c ≤ hi := by
  have ha₁ := quadratic_nonpos_leading a b (c-hi) (fun n => by have := (h n).2; linarith)
  have ha₂ := quadratic_nonpos_leading (-a) (-b) (lo-c) (fun n => by have := (h n).1; nlinarith)
  have ha : a = 0 := by omega
  subst a
  simp only [zero_mul,zero_add] at h
  have hb₁ := linear_nonpos_leading b (c-hi) (fun n => by have := (h n).2; omega)
  have hb₂ := linear_nonpos_leading (-b) (lo-c) (fun n => by have := (h n).1; nlinarith)
  have hb : b = 0 := by omega
  subst b
  simpa using h 0

lemma quadratic_growth_compare (f g : ℕ → ℕ) (a d b c e z : ℤ)
    (hf : ∀ n : ℕ, a*(n:ℤ)^2+b*n+c ≤ 2*(f n:ℤ))
    (hg : ∀ n, 2*(g n:ℤ) ≤ d*(n:ℤ)^2+e*n+z)
    (hfg : ∀ n, f n ≤ g n) : a ≤ d := by
  have H := quadratic_nonpos_leading (a-d) (b-e) (c-z) (fun n => by
    have h₁ := hf n
    have h₂ := hg n
    have h₃ : (f n:ℤ) ≤ g n := by exact_mod_cast hfg n
    nlinarith only [h₁,h₂,h₃])
  omega
end MaximalSeshadri.NefNumerics

end



end OAI
