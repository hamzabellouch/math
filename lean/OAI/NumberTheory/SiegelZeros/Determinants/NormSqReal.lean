import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Selection.RestrictWeightSortedEquiv

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open InnerProductSpace
namespace WeightedTorusJets

theorem norm_of_sq_eq_real {z : ℂ} {r : ℝ} (hz : z ^ 2 = (r : ℂ)) :
    ‖z‖ = Real.sqrt |r| := by
  rw [← Real.sqrt_sq (norm_nonneg z), ← norm_pow, hz, Complex.norm_real, Real.norm_eq_abs]

theorem norm_biquadratic_box_le {a b : ℂ} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n₁ n₂ n₃ n₄ : ℕ) (hn₁ : n₁ ≤ N) (hn₂ : n₂ ≤ N)
    (hn₃ : n₃ ≤ N) (hn₄ : n₄ ≤ N) :
    ‖(n₁ : ℂ) + n₂ * a + n₃ * b + n₄ * (a * b)‖ ≤
      8 * N * Real.sqrt q := by
  have hna : ‖a‖ ≤ Real.sqrt q := by
    rw [norm_of_sq_eq_real (r := (d : ℝ)) (by simpa using ha)]
    exact Real.sqrt_le_sqrt hd
  have hnb : ‖b‖ ≤ 2 := by
    rw [norm_of_sq_eq_real (r := 2) (by simpa using hb), Real.sqrt_le_iff]
    norm_num
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsq : 1 ≤ Real.sqrt q := (Real.one_le_sqrt).mpr hq'
  have hnN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hab : ‖a * b‖ ≤ 2 * Real.sqrt q := by
    simpa only [mul_comm] using norm_mul_le_of_le hna hnb
  calc
    ‖(n₁ : ℂ) + n₂ * a + n₃ * b + n₄ * (a * b)‖ ≤
        ‖(n₁ : ℂ)‖ + ‖(n₂ : ℂ) * a‖ + ‖(n₃ : ℂ) * b‖ +
          ‖(n₄ : ℂ) * (a * b)‖ := norm_add₄_le
    _ = n₁ + n₂ * ‖a‖ + n₃ * ‖b‖ + n₄ * ‖a * b‖ := by simp
    _ ≤ N + N * Real.sqrt q + N * 2 + N * (2 * Real.sqrt q) := by
      gcongr
    _ ≤ 8 * N * Real.sqrt q := by nlinarith [mul_le_mul_of_nonneg_left hsq hnN]

theorem norm_embedding_biquadratic_box_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) :
    ‖ν ((n 0 : K) + n 1 * a + n 2 * b + n 3 * (a * b))‖ ≤
      8 * N * Real.sqrt q := by
  simp only [map_add, map_mul, map_natCast]
  refine norm_biquadratic_box_le ?_ ?_ hd hq _ _ _ _
    (hn 0).le (hn 1).le (hn 2).le (hn 3).le
  · simpa using congrArg ν ha
  · simpa only [map_pow, map_ofNat] using congrArg ν hb

theorem norm_three_powers_le {x y z : ℂ} {B : ℝ}
    (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) (hz : ‖z‖ ≤ B)
    (i j k : ℕ) : ‖x ^ i * y ^ j * z ^ k‖ ≤ B ^ (i + j + k) := by
  have hB : 0 ≤ B := (norm_nonneg x).trans hx
  simp only [norm_mul, norm_pow, pow_add]
  gcongr

theorem norm_embedding_basis_sum_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) :
    ‖ν (∑ i : Fin 4, (n i : K) * ![1, a, b, a * b] i)‖ ≤
      8 * N * Real.sqrt q := by
  simpa [Fin.sum_univ_succ, add_assoc] using
    norm_embedding_biquadratic_box_le ν ha hb hd hq n hn

theorem norm_embedding_derivative_entry_le {K : Type*} [CommRing K]
    (ν : K →+* ℂ) (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (n : Fin 4 → ℕ) (hn : ∀ i, n i < N) (α : Fin 3 → ℕ) :
    let θ := ∑ i : Fin 4, (n i : K) * ![1, a, b, a * b] i
    ‖ν (θ ^ (α 0) * σ θ ^ (α 1) * (σ.comp τ) θ ^ (α 2))‖ ≤
      (8 * N * Real.sqrt q) ^ (α 0 + α 1 + α 2) := by
  dsimp only
  simp only [map_mul, map_pow]
  apply norm_three_powers_le
  · exact norm_embedding_basis_sum_le ν ha hb hd hq n hn
  · exact norm_embedding_basis_sum_le (ν.comp σ) ha hb hd hq n hn
  · exact norm_embedding_basis_sum_le (ν.comp (σ.comp τ)) ha hb hd hq n hn

end WeightedTorusJets

open _root_.Finset

namespace WeightedTorusJets

variable {K : Type*} [Field K] [NumberField K]

theorem abs_field_norm_eq_prod_embeddings (a : K) :
    |(Algebra.norm ℚ a : ℝ)| = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ a‖ := by
  simpa only [eq_ratCast, Complex.norm_ratCast, norm_prod] using
    congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)

theorem log_abs_field_norm_eq_sum_embeddings {a : K} (ha : a ≠ 0) :
    Real.log |(Algebra.norm ℚ a : ℝ)| =
      ∑ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ a‖ := by
  rw [abs_field_norm_eq_prod_embeddings, Real.log_prod]
  simp [ha]

theorem quarter_log_field_norm_le_of_embeddings {a : K} (ha : a ≠ 0)
    (hdegree : Module.finrank ℚ K = 4) {B : ℝ}
    (hbound : ∀ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ a‖ ≤ B) :
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ a : ℝ)| ≤ B := by
  rw [log_abs_field_norm_eq_sum_embeddings ha]
  have hsum := Finset.sum_le_card_nsmul Finset.univ _ B (fun σ _ ↦ hbound σ)
  simp only [Finset.card_univ, AlgHom.card, hdegree, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  linarith

end WeightedTorusJets

namespace WeightedTorusJets

theorem archimedean_jet_determinant_bound {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q) (hN : 0 < N)
    (n : Fin (N ^ 4) → Fin 4 → ℕ) (hn : ∀ j i, n j i < N)
    (α : Fin (N ^ 4) → Fin 3 → ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    A.det ≠ 0 →
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ A.det : ℝ)| ≤
      ((N ^ 4 : ℕ) : ℝ) / 2 * Real.log (N ^ 4 : ℕ) +
        ((∑ i, α i 0 : ℕ) + (∑ i, (α i 1 + α i 2) : ℕ)) *
          (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  dsimp only
  intro hdet
  apply quarter_log_field_norm_le_of_embeddings hdet hdegree
  intro ν
  convert SiegelJets.log_norm_map_det_archimedean (pow_pos hN 4) hN
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hq) ν.toRingHom _ hdet
    (fun i => α i 0 + α i 1 + α i 2)
    (fun i j => norm_embedding_derivative_entry_le ν.toRingHom σ τ ha hb hd hq
      (n j) (hn j) (α i)) using 1
  simp only [Finset.sum_add_distrib, Nat.cast_add, add_assoc]



open scoped NumberField BigOperators

theorem archimedean_bound_of_integral_jet_determinant {K : Type*}
    [Field K] [NumberField K] (hdegree : Module.finrank ℚ K = 4)
    (σ τ : K →+* K) {a b : K} {d : ℤ} {q N : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hd : |(d : ℝ)| ≤ q) (hq : 1 ≤ q) (hN : 0 < N)
    (n : Fin (N ^ 4) → Fin 4 → ℕ) (hn : ∀ j i, n j i < N)
    (α : Fin (N ^ 4) → Fin 3 → ℕ) (Δ : 𝓞 K) (hne : Δ ≠ 0)
    (hΔ : (Δ : K) =
      Matrix.det (fun i j =>
        (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 0 *
        σ (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 1 *
        (σ.comp τ) (∑ k : Fin 4, (n j k : K) * ![1, a, b, a * b] k) ^ α i 2)) :
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| ≤
      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
          (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
  let A : Matrix (Fin (N ^ 4)) (Fin (N ^ 4)) K :=
    Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 * (σ.comp τ) (θ j) ^ α i 2
  change (Δ : K) = A.det at hΔ
  have hcast : (Δ : K) ≠ 0 := fun h => hne (Subtype.ext h)
  have hdet : A.det ≠ 0 := hΔ ▸ hcast
  have hbound := archimedean_jet_determinant_bound hdegree σ τ ha hb hd hq hN n hn α hdet
  change (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ A.det : ℝ)| ≤ _ at hbound
  rw [← hΔ] at hbound
  simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_add] using hbound

end WeightedTorusJets

open scoped BigOperators NumberField

namespace WeightedTorusJets

theorem quarter_log_field_norm_lower {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) (x : 𝓞 K) (hx : x ≠ 0)
    (P : Finset ℕ) (E : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hdvd : ∀ p ∈ P, (p : 𝓞 K) ^ E p ∣ x) :
    ∑ p ∈ P, (E p : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (x : K) : ℝ)| := by
  have hd : (∏ p ∈ P, (p : ℤ) ^ (4 * E p)) ∣ Algebra.norm ℤ x := by
    apply Finset.prod_dvd_of_coprime ?_ ?_
    · intro p hpm q hqm hpq
      exact ((Nat.coprime_primes (hp p hpm) (hp q hqm)).mpr hpq).isCoprime.pow
    · intro p hpm
      simpa [map_pow, Algebra.norm_natCast, NumberField.RingOfIntegers.rank,
        hdegree, ← pow_mul] using map_dvd (Algebra.norm ℤ) (hdvd p hpm)
  have hle : (∏ p ∈ P, p ^ (4 * E p)) ≤ (Algebra.norm ℤ x).natAbs := by
    simpa only [← Nat.cast_pow, ← Nat.cast_prod, Int.natAbs_natCast] using
      Int.natAbs_le_of_dvd_ne_zero hd (Algebra.norm_ne_zero_iff.mpr hx)
  have hpos : (0 : ℝ) < ∏ p ∈ P, (p : ℝ) ^ (4 * E p) :=
    Finset.prod_pos fun p hpm => pow_pos (by exact_mod_cast (hp p hpm).pos) _
  have hlog := Real.log_le_log (y := ((Algebra.norm ℤ x).natAbs : ℝ)) hpos
    (by exact_mod_cast hle)
  rw [Real.log_prod (fun p hpm => pow_ne_zero _
    (by exact_mod_cast (hp p hpm).ne_zero))] at hlog
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat, mul_assoc,
    ← Finset.mul_sum] at hlog
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
  linarith

theorem prime_floor_sum_lower_raw {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (U : ℝ) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE ⌊U⌋₊) :
    (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
      ∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p := by
  have hlog : (∑ p ∈ P, Real.log p) ≤ ∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => Real.log_natCast_nonneg p)
  calc
    _ ≤ (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ P, Real.log p) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg s.card)) _
    _ = ∑ p ∈ P, ((∑ i ∈ s, (a i : ℝ)) / p - s.card) * Real.log p := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
      have h := Finset.sum_le_sum (s := s)
        (fun i _ => (Nat.sub_one_lt_floor ((a i : ℝ) / p)).le)
      simpa [Finset.sum_sub_distrib, ← Finset.sum_div, Nat.floor_div_eq_div] using h

theorem finite_place_raw_norm_bounds {K ι : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) (Δ : 𝓞 K) (hΔ : Δ ≠ 0)
    (s : Finset ι) (a : ι → ℕ) (U : ℝ) (P : Finset ℕ)
    (hP : P ⊆ Nat.primesLE ⌊U⌋₊)
    (hdiv : ∀ p ∈ P, (p : 𝓞 K) ^ (∑ i ∈ s, a i / p) ∣ Δ) :
    (∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) ∧
    ((∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        (s.card : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
      ∑ p ∈ P, ((∑ i ∈ s, a i / p : ℕ) : ℝ) * Real.log p) :=
  ⟨quarter_log_field_norm_lower hdegree Δ hΔ P (fun p => ∑ i ∈ s, a i / p)
      (fun _ hp => Nat.prime_of_mem_primesLE (hP hp)) hdiv,
    prime_floor_sum_lower_raw s a U P hP⟩



theorem prime_floor_sum_lower {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    {U : ℝ} (hU : 0 ≤ U) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE ⌊U⌋₊) :
    (∑ i ∈ s, (a i : ℝ)) * (∑ p ∈ P, Real.log p / (p : ℝ)) -
        Real.log 4 * s.card * U ≤
      ∑ p ∈ P, (∑ i ∈ s, ((a i / p : ℕ) : ℝ)) * Real.log p := by
  have hlog : (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤ Real.log 4 * U := by
    rw [← Chebyshev.theta_eq_sum_primesLE]
    exact Chebyshev.theta_le_log4_mul_x hU
  have hraw := prime_floor_sum_lower_raw s a U P hP
  simp only [Nat.cast_sum] at hraw
  apply le_trans _ hraw
  apply sub_le_sub_left
  convert mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg s.card) using 1
  ring



open scoped BigOperators NumberField

theorem finite_place_bounds_of_source_determinant {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) {m : ℕ}
    (Δ : 𝓞 K) (hΔ : Δ ≠ 0) (α : Fin m → Fin 3 → ℕ)
    (q H : ℕ) (χ : ℕ → ℂ)
    (hdiv : ∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ p = -1 →
      Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p))
    (U : ℝ) (hU : 0 ≤ U) :
    let P := (Nat.primesLE ⌊U⌋₊).filter
      (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
    let E := fun p => ∑ i, α i 0 / p
    let S₁ := ∑ i, (α i 0 : ℝ)
    (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) ∧
    (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
      (m : ℝ) * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
        ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
    (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) - Real.log 4 * m * U ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|) := by
  dsimp only
  let P := (Nat.primesLE ⌊U⌋₊).filter
    (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
  have hdiv' (p : ℕ) (hp : p ∈ P) : (p : 𝓞 K) ^ (∑ i, α i 0 / p) ∣ Δ := by
    obtain ⟨hpprime, hH, hpq, hχ⟩ := Finset.mem_filter.mp hp
    simpa only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using
      hdiv p (Nat.prime_of_mem_primesLE hpprime) hH hpq hχ
  have hraw := finite_place_raw_norm_bounds hdegree Δ hΔ Finset.univ
    (fun i => α i 0) U P (Finset.filter_subset _ _) hdiv'
  simp only [Finset.card_univ, Fintype.card_fin] at hraw
  refine ⟨hraw.1, hraw.2, ?_⟩
  have hcheb := prime_floor_sum_lower Finset.univ (fun i => α i 0)
    hU P (Finset.filter_subset _ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hcheb
  exact hcheb.trans (by simpa only [Nat.cast_sum] using hraw.1)

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_character_global_greedy_determinant_local_bounds (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) *
                ![1, a', b', a' * b'] i
              let R := fun α : Fin 3 → ℕ => fun j =>
                θ j ^ α 0 * σ (θ j) ^ α 1 * (σ * τ) (θ j) ^ α 2
              let s := weightedJetIndices H (N ^ 4 - 1)
              let w := fun α : Fin 3 → ℕ => α 0 + H * α 1 + H * α 2
              ∀ e : ℕ ≃ (Fin 3 → ℕ), Monotone (fun i => w (e i)) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ e) s.card : Set ℕ) ∧
                  (∀ i, α i = e (g i)) ∧
                  Set.range α = ((greedyPivots B (R ∘ e) s.card).image e : Set (Fin 3 → ℕ)) ∧
                  Monotone (fun i => w (α i)) ∧ (∀ i, w (α i) ≤ N ^ 4 - 1) ∧
                  (∀ t : ℕ, s.card ≤ t →
                    Set.range g = (greedyPivots B (R ∘ e) t : Set ℕ)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
                    Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) ∧
                    ∀ U : ℝ, 0 ≤ U →
                      let P := (Nat.primesLE ⌊U⌋₊).filter
                        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)
                      let E := fun p => ∑ i, α i 0 / p
                      let S₁ := ∑ i, (α i 0 : ℝ)
                      (∑ p ∈ P, (E p : ℝ) * Real.log p ≤
                        (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        (N : ℝ) ^ 4 * (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤
                          ∑ p ∈ P, (E p : ℝ) * Real.log p) ∧
                      (S₁ * (∑ p ∈ P, Real.log p / (p : ℝ)) -
                        Real.log 4 * (N : ℝ) ^ 4 * U ≤
                          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)|) := by
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    source_character_global_greedy_determinant_divisibility q χ hreal hprim hne hfield
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro e he
  obtain ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ, hdiv⟩ :=
    hsource N H hH n e he
  refine ⟨g, α, hg, hα, hrange, hmono, hweight, hstable, Δ, hΔ, hneΔ, ?_, hdiv, ?_⟩
  · let B := IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    have ha' : a' ^ 2 = (d : B) := by apply Subtype.ext; exact ha
    have hb' : b' ^ 2 = (2 : B) := by apply Subtype.ext; exact hb
    have hdreal : |(d : ℝ)| ≤ q := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using
        (show (d.natAbs : ℝ) ≤ q from Nat.cast_le.mpr hbound)
    exact archimedean_bound_of_integral_jet_determinant hdegree σ.toRingHom τ.toRingHom
      ha' hb' hdreal (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (hH.trans_le hHN)
      (fun j i => (n j i : ℕ)) (fun j i => (n j i).isLt) α Δ hneΔ hΔ

  · intro U hU
    simpa only [Nat.cast_pow] using finite_place_bounds_of_source_determinant hdegree
      Δ hneΔ α q H (fun p => χ p) hdiv U hU

end WeightedTorusJets

namespace WeightedTorusJets

open scoped BigOperators NumberField

theorem finite_place_lower_of_source_determinant {K : Type*} [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) {m : ℕ}
    (Δ : 𝓞 K) (hΔ : Δ ≠ 0) (α : Fin m → Fin 3 → ℕ)
    (q H : ℕ) (χ : ℕ → ℂ)
    (hdiv : ∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ p = -1 →
      Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p))
    {U C ell delta CH : ℝ} (hU : 0 ≤ U) (hC : Real.log 4 ≤ C)
    (hbias : Real.log U - C * ell - C * delta * (Real.log U) ^ 2 / ell - CH ≤
      ∑ p ∈ (Nat.primesLE ⌊U⌋₊).filter
        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1), Real.log p / (p : ℝ)) :
    (∑ i, (α i 0 : ℝ)) *
        (Real.log U - C * ell - C * delta * (Real.log U) ^ 2 / ell - CH) -
      C * m * U ≤ (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| := by
  have hbound := (finite_place_bounds_of_source_determinant
    hdegree Δ hΔ α q H χ hdiv U hU).2.2
  refine le_trans ?_ hbound
  exact sub_le_sub
    (mul_le_mul_of_nonneg_left hbias (Finset.sum_nonneg fun i _ => Nat.cast_nonneg (α i 0)))
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg m)) hU)

theorem three_le_level_of_nonprincipal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) : 3 ≤ q := by
  by_contra hq
  have hq0 : q ≠ 0 := NeZero.ne q
  have hsmall : q = 1 ∨ q = 2 := by omega
  rcases hsmall with rfl | rfl
  · exact hne (DirichletCharacter.level_one χ)
  · apply hne
    apply MulChar.eq_one_iff.mpr
    intro u
    rw [(by decide : ∀ u : (ZMod 2)ˣ, u = 1) u]
    simp

end WeightedTorusJets

namespace WeightedTorusJets

open scoped BigOperators NumberField

theorem source_given_determinant_finite_lower_of_real_zero :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
      ∀ H : ℕ, ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q,
          χ.IsPrimitive → χ ≠ 1 → (∀ x : ZMod q, (χ x).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℚ K = 4 →
        ∀ (m : ℕ) (Δ : 𝓞 K), Δ ≠ 0 → ∀ α : Fin m → Fin 3 → ℕ,
          (∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ (p : ZMod q) = -1 →
            Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p)) →
        ∀ U : ℝ, 0 ≤ U →
          (∑ i, (α i 0 : ℝ)) *
              (Real.log U - C * Real.log q -
                C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH) -
            C * m * U ≤ (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| := by
  obtain ⟨C, hC, hC4, hmass⟩ := source_good_prime_mass_all_parameters
  refine ⟨C, hC, hC4, ?_⟩
  intro H
  obtain ⟨CH, hCH⟩ := hmass H
  refine ⟨CH, ?_⟩
  intro q _ χ hprim hne hreal β hβ0 hβ1 hzero K _ _ hdegree m Δ hΔ α hdiv U hU
  exact finite_place_lower_of_source_determinant hdegree Δ hΔ α q H
    (fun p => χ (p : ZMod q)) hdiv hU hC4
    (hCH q (three_le_level_of_nonprincipal χ hne) χ hprim hne hreal
      β hβ0 hβ1 hzero U hU)

end WeightedTorusJets


end SiegelZeros

end OAI
