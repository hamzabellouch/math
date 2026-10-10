import OAI.Dynamics.StandardMap.MeanCancellation

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def meanLoss (k : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)-∫ z,productDistance k z 0 (n:ℤ) ∂area
lemma meanLoss_nonneg (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : 0 ≤ meanLoss k n :=
  sub_nonneg.mpr (integral_productDistance_bounds k hk n).2
lemma meanLoss_eq (k : ℝ) (n : ℕ) : meanLoss k n=(n:ℝ)*meanDeficit k n := by
  cases n with
  | zero => simp [meanLoss,meanDeficit]
  | succ n => unfold meanLoss meanDeficit; field_simp
lemma meanLoss_superadditive (k : ℝ) (hk : 0 ≤ k) (n m : ℕ) :
    meanLoss k n+meanLoss k m ≤ meanLoss k (n+m) := by
  have hi := integral_mono (integrable_productDistance k hk 0 ((n+m:ℕ):ℤ))
    ((integrable_productDistance k hk 0 (n:ℤ)).add (integrable_productDistance k hk (n:ℤ) ((n+m:ℕ):ℤ)))
    (fun z => productDistance_triangle k hk z 0 (n:ℤ) ((n+m:ℕ):ℤ))
  have he : (∫ z,productDistance k z 0 (n:ℤ)+productDistance k z (n:ℤ) ((n+m:ℕ):ℤ) ∂area)=
      (∫ z,productDistance k z 0 (n:ℤ) ∂area)+(∫ z,productDistance k z 0 (m:ℤ) ∂area) := by
    rw [integral_add (integrable_productDistance k hk 0 _) (integrable_productDistance k hk _ _)]
    congr 1
    simpa only [zero_add,add_zero,Nat.cast_add,add_comm] using integral_distance_shift k 0 (m:ℤ) (n:ℤ)
  simp only [Pi.add_apply] at hi
  rw [he] at hi
  unfold meanLoss
  simp only [Nat.cast_add] at hi ⊢
  linarith
lemma meanLoss_mono (k : ℝ) (hk : 0 ≤ k) : Monotone (meanLoss k) := by
  intro n m hnm
  have hh := meanLoss_superadditive k hk n (m-n)
  rw [Nat.add_sub_of_le hnm] at hh
  linarith [meanLoss_nonneg k hk (m-n)]
lemma meanDeficit_comparison (k : ℝ) (hk : 0 ≤ k) (n m : ℕ) (hnm : n ≤ m) :
    (n:ℝ)*meanDeficit k n ≤ (m:ℝ)*meanDeficit k m := by
  simpa only [← meanLoss_eq] using meanLoss_mono k hk hnm
lemma meanDeficit_pow_mono (k : ℝ) (hk : 0 ≤ k) : Monotone (fun j : ℕ => meanDeficit k (2^j)) := by
  apply monotone_nat_of_le_succ
  intro j
  have hh := meanDeficit_doubling_mono k hk (2^j) (by positivity)
  simpa only [pow_succ,Nat.mul_two] using hh
lemma first_dyadic_crossing (k θ C : ℝ) (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p : ℕ) (hp : meanDeficit k (2^p) ≤ θ)
    (hex : ∃ q : ℕ, θ < meanDeficit k (2^q)) :
    ∃ q : ℕ, p < q ∧ θ < meanDeficit k (2^q) ∧
      (∀ j, j < q → meanDeficit k (2^j) ≤ θ) ∧
      meanDeficit k (2^q) ≤ C*θ+C/((2^p:ℕ):ℝ) := by
  let q := Nat.find hex
  have hq : θ < meanDeficit k (2^q) := Nat.find_spec hex
  have hprev (j : ℕ) (hj : j < q) : meanDeficit k (2^j) ≤ θ :=
    le_of_not_gt (Nat.find_min hex hj)
  have hpq : p < q := by
    by_contra h
    have hle := meanDeficit_pow_mono k hk (show q ≤ p by omega)
    linarith
  refine ⟨q,hpq,hq,hprev,?_⟩
  have hq0 : 0 < q := by omega
  have hm := hdouble (2^(q-1)) (by positivity)
  have he : 2^(q-1)+2^(q-1)=2^q := by
    rw [← Nat.mul_two,← pow_succ]
    congr 1; omega
  rw [he] at hm
  have hθ := mul_le_mul_of_nonneg_left (hprev (q-1) (by omega)) hC
  have hpow : ((2^p:ℕ):ℝ) ≤ ((2^(q-1):ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (show p ≤ q-1 by omega)
  have hd : C/((2^(q-1):ℕ):ℝ) ≤ C/((2^p:ℕ):ℝ) :=
    div_le_div_of_nonneg_left hC (by positivity) hpow
  linarith
end StandardMapEntropy

end OAI
