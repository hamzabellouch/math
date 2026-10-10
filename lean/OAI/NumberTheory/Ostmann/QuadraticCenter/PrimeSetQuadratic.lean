import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDensityCorrelation
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedCorrelationEnergy
import OAI.NumberTheory.Ostmann.QuadraticCenter.LowWeightEulerBound

namespace OAI

/-! # Actual quadratic density sums indexed by prime divisors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

theorem primeSet_list_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ P.toList, p.Prime := fun p hp => hP p (Finset.mem_toList.mp hp)

theorem primeSet_list_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    P.toList.Pairwise Nat.Coprime := by
  apply List.Pairwise.imp_of_mem _ P.nodup_toList
  intro p q hp hq hpq
  exact (Nat.coprime_primes (hP p (Finset.mem_toList.mp hp))
    (hP q (Finset.mem_toList.mp hq))).mpr hpq

noncomputable def primeSetQuadraticSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ)
    (a : ZMod P.toList.prod) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ) : ℂ :=
  let : NeZero P.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime P hP)).ne'⟩
  quadraticDensitySum
    (densityFourier (densityCRTList _ (primeSet_list_prime P hP) (primeSet_list_coprime P hP) S).value)
    W a θ Φ R v s

theorem support_correlation_product (P U V : Finset ℕ) (hU : U ⊆ P) (hV : V ⊆ P) :
    ((U ∪ V).toList.map (correlationPrimeBound (supportCorrelationSide U V))).prod =
      ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then (1 : ℝ) else (Real.sqrt (p : ℝ))⁻¹ := by
  classical
  rw [← List.prod_toFinset _ (U ∪ V).nodup_toList, Finset.toList_toFinset]
  have hsub : U ∪ V ⊆ P := Finset.union_subset hU hV
  have heq : (∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then (1 : ℝ) else (Real.sqrt (p : ℝ))⁻¹) =
      ∏ p ∈ U ∪ V, if (p ∈ U ↔ p ∈ V) then (1 : ℝ) else (Real.sqrt (p : ℝ))⁻¹ := by
    apply (Finset.prod_subset hsub _).symm
    intro p hp hnot
    have hu : p ∉ U := fun hh => hnot (Finset.mem_union_left V hh)
    have hv : p ∉ V := fun hh => hnot (Finset.mem_union_right U hh)
    simp [hu, hv]
  rw [heq]
  apply Finset.prod_congr rfl
  intro p hp
  have hm := Finset.mem_union.mp hp
  unfold supportCorrelationSide correlationPrimeBound
  rcases hm with hu | hv
  · by_cases hv : p ∈ V <;> simp [hu, hv]
  · by_cases hu : p ∈ U <;> simp [hu, hv]

theorem primeSet_prod_le_of_subset (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) : U.toList.prod ≤ P.toList.prod := by
  have he (Q : Finset ℕ) : Q.toList.prod = ∏ p ∈ Q, p := by
    simp
  rw [he, he]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ hU (fun _ _ => Nat.zero_le _)
    (fun p hp _ => (hP p hp).one_lt.le)

theorem primeSet_prod_dvd_of_subset (P U : Finset ℕ) (hU : U ⊆ P) :
    U.toList.prod ∣ P.toList.prod := by
  simpa using Finset.prod_dvd_prod_of_subset U P (fun p : ℕ => p) hU

theorem primeSetQuadraticSum_eq_unit_waves (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ)
    (a : ZMod U.toList.prod) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ)
    (hW : ∀ w ∈ W, 0 < w) (hR : 0 < R) (hv : 0 < v) :
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hU)).ne'⟩
    primeSetQuadraticSum U hU S W a θ Φ R v s =
      normalizedDensityWaveSum
        (densityFourier (densityCRTList U.toList (primeSet_list_prime U hU) (primeSet_list_coprime U hU) S).value)
        (unitQuadraticSupport W a) (quadraticUnitScalar a) Φ
        (fun w => θ * v * (w : ℝ) ^ 2 / U.toList.prod)
        (fun w => R * U.toList.prod / (v * (w : ℝ) ^ 2)) R v s := by
  intro _
  exact quadraticDensitySum_eq_unit_waves _
    (densityCRTList U.toList (primeSet_list_prime U hU) (primeSet_list_coprime U hU) S).fourier_nonunit
    W a θ Φ R v s hW hR hv

/-- The pair bound for actual prime-divisor sums, with the common modulus
and exclusive-prime factor obtained from their prime sets. -/
theorem primeSet_quadratic_correlation (P U V : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) (hV : V ⊆ P)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W Vw : Finset ℕ)
    (a : ZMod U.toList.prod) (b : ZMod V.toList.prod) (Φ Ψ : 𝓢(ℝ, ℂ))
    (θ η R v C : ℝ) (M N : ℕ) (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C)
    (hM : 0 < M) (hN : 0 < N) (hperiod : P.toList.prod ^ 2 ≤ N)
    (hW : ∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * U.toList.prod / ((N : ℝ) * v))
    (hVw : ∀ w ∈ Vw, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * V.toList.prod / ((N : ℝ) * v)) :
    ‖∑ n ∈ Finset.range N,
      primeSetQuadraticSum U (fun p hp => hP p (hU hp)) S W a θ Φ R v (n + M) *
      conj (primeSetQuadraticSum V (fun p hp => hP p (hV hp)) S Vw b η Ψ R v (n + M)) /
        ((n + M : ℕ) : ℂ)‖ ≤
      C * (4 * correlationWeightBudget Φ Ψ C C) *
        ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹ := by
  have hUV : U ∪ V ⊆ P := Finset.union_subset hU hV
  have hpU : ∀ p ∈ U, p.Prime := fun p hp => hP p (hU hp)
  have hpV : ∀ p ∈ V, p.Prime := fun p hp => hP p (hV hp)
  have hpUV : ∀ p ∈ U ∪ V, p.Prime := fun p hp => hP p (hUV hp)
  have hb := quadratic_density_correlation_bound U.toList V.toList (U ∪ V).toList
    (primeSet_list_prime U hpU) (primeSet_list_prime V hpV) (primeSet_list_prime _ hpUV)
    (primeSet_list_coprime U hpU) (primeSet_list_coprime V hpV) (primeSet_list_coprime _ hpUV)
    (by simp) S W Vw a b Φ Ψ θ η R v C M N hR hv hC hM hN
    ((Nat.pow_le_pow_left (primeSet_prod_le_of_subset P (U ∪ V) hP hUV) 2).trans hperiod) hW hVw
  simpa only [primeSetQuadraticSum, Finset.toList_toFinset,
    support_correlation_product P U V hU hV] using hb

end Ostmann

end OAI
