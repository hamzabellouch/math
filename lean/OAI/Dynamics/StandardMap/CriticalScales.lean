import OAI.Dynamics.StandardMap.FixedDeficit

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma exists_dyadic_ceiling (n : ℕ) (hn : 0 < n) : ∃ q : ℕ, n ≤ 2^q ∧ 2^q < 2*n := by
  have hx : ∃ q : ℕ, n ≤ 2^q := ⟨n,by
    have hh := (Nat.lt_two_pow_self (n := n))
    omega⟩
  let q := Nat.find hx
  have hl : n ≤ 2^q := Nat.find_spec hx
  refine ⟨q,hl,?_⟩
  by_cases hq : q=0
  · simp only [hq,pow_zero]; omega
  · have hp : 2^(q-1) < n := lt_of_not_ge (Nat.find_min hx (show q-1 < q by omega))
    have he : 2^q=2^(q-1)*2 := by rw [← pow_succ]; congr 1; omega
    rw [he]; omega
lemma positive_deficit_dyadic (k η : ℝ) (hk : 0 ≤ k) (hη : 0 < η)
    (hex : ∃ n : ℕ, 0 < n ∧ η ≤ meanDeficit k n) :
    ∃ q : ℕ, η/2 < meanDeficit k (2^q) := by
  obtain ⟨n,hn,hnη⟩ := hex
  obtain ⟨q,hq,hq2⟩ := exists_dyadic_ceiling n hn
  have hh := meanDeficit_comparison k hk n (2^q) hq
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hqR : ((2^q:ℕ):ℝ) < 2*(n:ℝ) := by exact_mod_cast hq2
  have hp : (0:ℝ) < (2^q:ℕ) := by positivity
  have he : 0 ≤ meanDeficit k (2^q) := (meanDeficit_bounds k hk _ (by positivity)).1
  refine ⟨q,?_⟩
  nlinarith
lemma meanDeficit_iterated_doubling (k C : ℝ) (hk : 0 ≤ k) (hC : 1 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p m : ℕ) :
    meanDeficit k (2^(p+m)) ≤ (2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)) := by
  have hp : (0:ℝ) < (2^p:ℕ) := by positivity
  have he0 := (meanDeficit_bounds k hk (2^p) (by positivity)).1
  induction m with
  | zero => simp only [Nat.add_zero,pow_zero,one_mul]; linarith [one_div_nonneg.mpr hp.le]
  | succ m ih =>
    have hh := hdouble (2^(p+m)) (by positivity)
    rw [show 2^(p+(m+1))=2^(p+m)+2^(p+m) by rw [show p+(m+1)=(p+m)+1 by omega,pow_succ,Nat.mul_two]]
    have hpM : ((2^p:ℕ):ℝ) ≤ ((2^(p+m):ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : p ≤ p+m)
    have hd : C/((2^(p+m):ℕ):ℝ) ≤ C/((2^p:ℕ):ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hp hpM
    have hpow : (1:ℝ) ≤ (2*C)^m := one_le_pow₀ (by linarith)
    have ht := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ C)
    rw [pow_succ]
    have hz : 0 ≤ 1/((2^p:ℕ):ℝ) := by positivity
    have hB : 1/((2^p:ℕ):ℝ) ≤ (2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)) := by nlinarith
    have hhB := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ C)
    calc
      _ ≤ C*meanDeficit k (2^(p+m))+C/((2^(p+m):ℕ):ℝ) := hh
      _ ≤ C*((2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)))+C/((2^p:ℕ):ℝ) := add_le_add ht hd
      _ ≤ _ := by simp only [div_eq_mul_inv] at hhB ⊢; nlinarith

lemma critical_scale_finite (k C θ : ℝ) (hk : 0 ≤ k) (hC : 1 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p : ℕ) (hp : meanDeficit k (2^p) ≤ θ^2) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hex : ∃ q : ℕ, θ < meanDeficit k (2^q)) :
    ∃ q : ℕ, p < q ∧ θ < meanDeficit k (2^q) ∧
      meanDeficit k (2^q) ≤ C*θ+C/((2^p:ℕ):ℝ) ∧
      (∀ m : ℕ, meanDeficit k (2^(p+m)) ≤ (2*C)^m*(θ^2+1/((2^p:ℕ):ℝ))) ∧
      (∀ m : ℕ, meanDeficit k (2^(q+m)) ≤ (2*C)^m*(meanDeficit k (2^q)+1/((2^p:ℕ):ℝ))) := by
  obtain ⟨q,hpq,hq,hprev,hup⟩ := first_dyadic_crossing k θ C hk (by linarith) hdouble p (by nlinarith) hex
  refine ⟨q,hpq,hq,hup,?_,?_⟩
  · intro m
    exact (meanDeficit_iterated_doubling k C hk hC hdouble p m).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  · intro m
    have hpqR : ((2^p:ℕ):ℝ) ≤ ((2^q:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hpq.le
    have hd : 1/((2^q:ℕ):ℝ) ≤ 1/((2^p:ℕ):ℝ) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpqR
    exact (meanDeficit_iterated_doubling k C hk hC hdouble q m).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
end StandardMapEntropy

end OAI
