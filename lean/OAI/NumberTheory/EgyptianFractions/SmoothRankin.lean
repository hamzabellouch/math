import Mathlib

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- A finite nonnegative sum over smooth numbers is bounded by the finite
Euler product. Only the local prime-power series need to be summable. -/
theorem smooth_sum_le_euler_product
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖f (p ^ j)‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, f n) ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := by
  classical
  obtain ⟨_, hprod⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hsum N
  calc
    (∑ n ∈ s, f n) = ∑ n ∈ s.subtype (fun n => n ∈ N.smoothNumbers), f n :=
      (Finset.sum_subtype_of_mem f hs).symm
    _ ≤ ∑' n : N.smoothNumbers, f n :=
      hprod.summable.sum_le_tsum _ (fun n _ => hf n)
    _ = ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := hprod.tsum_eq

/-- The elementary exponential weight used in Rankin's tail estimate. -/
theorem rankin_weight_bound {V β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hn : Real.exp V ≤ (n : ℝ)) :
    1 ≤ Real.exp (-β * V) * (n : ℝ) ^ β := by
  have hpow := Real.rpow_le_rpow (le_of_lt (Real.exp_pos V)) hn hβ
  rw [← Real.exp_mul] at hpow
  have h := mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos (-β * V)))
  have hid : Real.exp (-β * V) * Real.exp (V * β) = 1 := by
    rw [← Real.exp_add]
    have : -β * V + V * β = 0 := by ring
    rw [this, Real.exp_zero]
  rwa [hid] at h

/-- Rankin's trick followed by a finite Euler product. This form applies to
`f n = τ(n)^r / n`; the local weight then has exponent `-1 + β`. -/
theorem smooth_rankin_bound
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    {V β : ℝ} (hβ : 0 ≤ β)
    (hsum : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, f n) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) := by
  have hg : ∀ n : ℕ, 0 ≤ f n * (n : ℝ) ^ β := by
    intro n
    exact mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) β)
  have hg1 : f 1 * (1 : ℝ) ^ β = 1 := by simp [hf1]
  have hgmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      f (m * n) * ((m * n : ℕ) : ℝ) ^ β =
        (f m * (m : ℝ) ^ β) * (f n * (n : ℝ) ^ β) := by
    intro m n hmn
    rw [hmul hmn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have heuler := smooth_sum_le_euler_product (fun n => f n * (n : ℝ) ^ β)
    hg (by simpa using hg1) hgmul hsum N s hs
  calc
    (∑ n ∈ s, f n) ≤ ∑ n ∈ s, Real.exp (-β * V) * (f n * (n : ℝ) ^ β) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_left (rankin_weight_bound hβ (hlarge n hn)) (hf n)
      nlinarith
    _ = Real.exp (-β * V) * ∑ n ∈ s, f n * (n : ℝ) ^ β := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-β * V) *
        (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left heuler (le_of_lt (Real.exp_pos _))

/-- The multiplicative weight occurring in divisor harmonic moments. -/
def divisorHarmonicWeight (r n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ r / (n : ℝ)

theorem divisorHarmonicWeight_nonneg (r n : ℕ) : 0 ≤ divisorHarmonicWeight r n := by
  unfold divisorHarmonicWeight
  positivity

theorem divisorHarmonicWeight_one (r : ℕ) : divisorHarmonicWeight r 1 = 1 := by
  simp [divisorHarmonicWeight]

theorem divisorHarmonicWeight_mul (r : ℕ) {m n : ℕ} (h : m.Coprime n) :
    divisorHarmonicWeight r (m * n) = divisorHarmonicWeight r m * divisorHarmonicWeight r n := by
  simp only [divisorHarmonicWeight, h.card_divisors_mul, Nat.cast_mul, mul_pow]
  ring

theorem divisorHarmonicWeight_prime_power (r : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ)
    (β : ℝ) :
    divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β =
      ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (0 : ℝ) < (p : ℝ) ^ j := pow_pos hpR j
  simp only [divisorHarmonicWeight, Nat.divisors_prime_pow hp, Finset.card_map,
    Finset.card_range, Nat.cast_pow]
  rw [Real.rpow_pow_comm (le_of_lt hpR), Real.rpow_sub_one (ne_of_gt hpow)]
  ring

theorem summable_successor_pow_geometric (r : ℕ) {q : ℝ} (hq : 0 < q) (hqone : q < 1) :
    Summable (fun j : ℕ => ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hqone
  have h := (summable_norm_pow_mul_geometric_of_norm_lt_one r hnorm).comp_injective
    Nat.succ_injective
  have h' := h.mul_right q⁻¹
  apply h'.congr
  intro j
  change ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ (j + 1)‖ * q⁻¹ =
    ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖
  rw [pow_succ, ← mul_assoc, norm_mul, Real.norm_eq_abs q, abs_of_pos hq]
  field_simp

theorem divisorHarmonicWeight_local_summable (r : ℕ) {β : ℝ} (hβ : β < 1)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => ‖divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖) := by
  simp_rw [divisorHarmonicWeight_prime_power r hp]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact summable_successor_pow_geometric r (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith))

/-- Concrete smooth-prefix Rankin estimate for any natural moment order. -/
theorem divisor_smooth_rankin_bound (r : ℕ) {V β : ℝ} (hβ : 0 ≤ β) (hβone : β < 1)
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ,
        ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j) := by
  have h := smooth_rankin_bound (divisorHarmonicWeight r) (divisorHarmonicWeight_nonneg r)
    (divisorHarmonicWeight_one r) (divisorHarmonicWeight_mul r) hβ
    (divisorHarmonicWeight_local_summable r hβone) N s hs hlarge
  change (∑ n ∈ s, divisorHarmonicWeight r n) ≤ _
  apply h.trans_eq
  apply congrArg (fun x : ℝ => Real.exp (-β * V) * x)
  apply Finset.prod_congr rfl
  intro p hp
  apply tsum_congr
  intro j
  exact divisorHarmonicWeight_prime_power r (Nat.prime_of_mem_primesBelow hp) j β

/-- The unweighted finite Euler-product bound for harmonic divisor moments. -/
theorem divisor_harmonic_sum_le_euler_product (r N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      ∏ p ∈ N.primesBelow, ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ)⁻¹) ^ j := by
  have hlarge : ∀ n ∈ s, Real.exp (0 : ℝ) ≤ (n : ℝ) := by
    intro n hn
    rw [Real.exp_zero]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_mem_smoothNumbers (hs n hn))
  simpa [Real.rpow_neg_one] using divisor_smooth_rankin_bound r (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    N s hs hlarge

/-- A local Euler factor, in the indexing convenient for Rankin's trick. -/
def divisorEulerFactor (r p : ℕ) (β : ℝ) : ℝ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j

theorem divisorEulerFactor_one_le (r : ℕ) {p : ℕ} (hp : p.Prime) {β : ℝ}
    (hβ : β < 1) : 1 ≤ divisorEulerFactor r p β := by
  have hs := divisorHarmonicWeight_local_summable r hβ hp
  simp_rw [divisorHarmonicWeight_prime_power r hp] at hs
  have h := hs.of_norm.sum_le_tsum {0} (by
    intro j _
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity)
  simpa [divisorEulerFactor] using h

/-- Logarithmic local-factor estimates turn the Rankin Euler product into a
single exponential. This is the precise smooth-prefix bound used in the
divisor-moment decomposition. -/
theorem divisor_smooth_rankin_log_bound (r : ℕ) {V β C : ℝ}
    (hβ : 0 ≤ β) (hβone : β < 1) (N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ))
    (hlocal : ∀ p ∈ N.primesBelow,
      Real.log (divisorEulerFactor r p β) ≤ C * (p : ℝ) ^ (β - 1)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) := by
  have hpos : ∀ p ∈ N.primesBelow, 0 < divisorEulerFactor r p β := by
    intro p hp
    have := divisorEulerFactor_one_le r (Nat.prime_of_mem_primesBelow hp) hβone
    linarith
  have hprodpos : 0 < ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := Finset.prod_pos hpos
  have hlog : Real.log (∏ p ∈ N.primesBelow, divisorEulerFactor r p β) ≤
      C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1) := by
    rw [Real.log_prod (fun p hp => ne_of_gt (hpos p hp)), Finset.mul_sum]
    exact Finset.sum_le_sum hlocal
  have hprod := (Real.log_le_iff_le_exp hprodpos).mp hlog
  have hrank := divisor_smooth_rankin_bound r hβ hβone N s hs hlarge
  change (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
    Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β at hrank
  calc
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := hrank
    _ ≤ Real.exp (-β * V) *
        Real.exp (C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      mul_le_mul_of_nonneg_left hprod (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      (Real.exp_add _ _).symm

end Problem337

end

end OAI
