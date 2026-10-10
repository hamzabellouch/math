import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCompactCutoff
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeSetQuadratic

namespace OAI

/-! # The small-kernel bound for the original positive quadratic series -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem positiveQuadraticSum_small_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0)
    (hq : (q : ℝ) ≤ Real.sqrt (R * q / ((s : ℝ) * v))) :
    ‖positiveQuadraticSum g a θ Φ R v s‖ ≤
      SchwartzMap.seminorm ℝ 0 0 Φ * (Real.sqrt H + 1) *
        Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) := by
  let Q := Real.sqrt (R * q / ((s : ℝ) * v))
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hQ : 0 < Q := Real.sqrt_pos.mpr (by positivity)
  let W := ⌊Real.sqrt (H * R * q / ((s : ℝ) * v))⌋₊
  let weight := fun w : ℕ => realAdditivePhase (θ * v * (w : ℝ) ^ 2 / q) ^ s *
    Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q))
  have hW : (W : ℝ) ≤ Real.sqrt H * Q := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans_eq
    have he : H * R * q / ((s : ℝ) * v) = H * (R * q / ((s : ℝ) * v)) := by ring
    rw [he, Real.sqrt_mul hH]
  have hw (w : ℕ) (_hw : w ∈ Finset.Ioc 0 W) :
      ‖weight w‖ ≤ SchwartzMap.seminorm ℝ 0 0 Φ := by
    simp only [weight, norm_mul, norm_pow, norm_realAdditivePhase, one_pow, one_mul]
    exact Φ.norm_le_seminorm ℝ _
  have hb := small_kernel_quadratic_sum_bound q W g hg henergy (a * (s : ZMod q)) weight
    (SchwartzMap.seminorm ℝ 0 0 Φ) (Real.sqrt H) Q (by positivity) hQ hq hW hw
  rw [positiveQuadraticSum_eq_cutoff g a θ Φ R v H s s hR hv hs le_rfl hΦ]
  have he : quadraticDensitySum g (quadraticCompactCutoff q R v H s) a θ Φ R v s =
      (Q : ℂ)⁻¹ * ∑ w ∈ Finset.Ioc 0 W, g ((a * (s : ZMod q)) * (w : ZMod q) ^ 2) * weight w := by
    unfold quadraticDensitySum
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    have hx : a * (w : ZMod q) ^ 2 * (s : ZMod q) =
        (a * (s : ZMod q)) * (w : ZMod q) ^ 2 := by ring
    simp only [quadraticDensityTerm, weight, hx]
    ring
  rw [he]
  exact hb

theorem sqrt_two_pow_succ (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (n + 1)) = Real.sqrt 2 * (Real.sqrt 2) ^ n := by
  have hp : ∀ n : ℕ, Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  rw [hp, pow_succ, mul_comm]

theorem primeSet_modulus_primeFactors (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) :
    U.toList.prod.primeFactors = U := by
  have he : U.toList.prod = ∏ p ∈ U, p := by simp
  rw [he, Nat.primeFactors_prod hU]

theorem primeSet_positive_small_bound (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ZMod U.toList.prod)
    (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0)
    (hq : (U.toList.prod : ℝ) ≤ Real.sqrt (R * U.toList.prod / ((s : ℝ) * v))) :
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hU)).ne'⟩
    ‖positiveQuadraticSum
      (densityFourier (densityCRTList U.toList (primeSet_list_prime U hU) (primeSet_list_coprime U hU) D).value)
      a θ Φ R v s‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 Φ * (Real.sqrt H + 1) * Real.sqrt 2) * (Real.sqrt 2) ^ U.card := by
  intro _
  have hb := positiveQuadraticSum_small_bound
    (densityFourier (densityCRTList U.toList (primeSet_list_prime U hU) (primeSet_list_coprime U hU) D).value)
    (densityCRTList U.toList (primeSet_list_prime U hU) (primeSet_list_coprime U hU) D).fourier_nonunit
    (densityCRTList_energy _ _ _ _) a θ Φ R v H s hR hv hH hs hΦ hq
  rw [primeSet_modulus_primeFactors U hU, sqrt_two_pow_succ] at hb
  exact hb.trans_eq (by ring)

end Ostmann

end OAI
