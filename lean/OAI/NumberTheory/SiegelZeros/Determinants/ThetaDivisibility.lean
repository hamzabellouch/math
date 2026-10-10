import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.SiegelZeros.Selection.RowReplacement

namespace OAI

namespace SiegelZeros


namespace Awei.W39

def theta {R : Type*} [CommRing R] (a b : R) (n : Fin 4 → ℤ) : R :=
  (n 0 : R) + (n 1 : R) * a + (n 2 : R) * b + (n 3 : R) * (a * b)

section CharacteristicP
variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

theorem legendre_cast_eq_pow (d : ℤ) :
    (legendreSym p d : R) = (d : R) ^ (p / 2) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) R) (legendreSym.eq_pow p d)
  simpa only [map_intCast, map_pow] using h

theorem root_pow_prime (hp : p ≠ 2) (a : R) (d : ℤ) (ha : a ^ 2 = (d : R)) :
    a ^ p = (legendreSym p d : R) * a := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp
  have he : 2 * (p / 2) + 1 = p := by
    simpa only [Nat.odd_iff.mp hodd] using Nat.div_add_mod p 2
  calc
    a ^ p = a ^ (2 * (p / 2) + 1) := congrArg (a ^ ·) he.symm
    _ = (a ^ 2) ^ (p / 2) * a := by rw [pow_add, pow_mul, pow_one]
    _ = (d : R) ^ (p / 2) * a := by rw [ha]
    _ = (legendreSym p d : R) * a := by rw [legendre_cast_eq_pow]

theorem intCast_pow_prime (n : ℤ) : (n : R) ^ p = (n : R) :=
  map_intCast (frobenius R p) n

theorem theta_pow_prime (hp : p ≠ 2) (a b : R) (d : ℤ)
    (ha : a ^ 2 = (d : R)) (hb : b ^ 2 = (2 : R)) (n : Fin 4 → ℤ) :
    theta a b n ^ p =
      theta ((legendreSym p d : R) * a) ((legendreSym p 2 : R) * b) n := by
  simp only [theta, add_pow_char, mul_pow, intCast_pow_prime,
    root_pow_prime p hp a d ha, root_pow_prime p hp b 2 (by simpa using hb)]

theorem theta_pow_prime_negative (hp : p ≠ 2) (a b : R) (d : ℤ)
    (ha : a ^ 2 = (d : R)) (hb : b ^ 2 = (2 : R))
    (hd : legendreSym p d = -1) (n : Fin 4 → ℤ) :
    theta a b n ^ p = theta (-a) ((legendreSym p 2 : R) * b) n := by
  simpa only [hd, Int.cast_neg, Int.cast_one, neg_one_mul] using
    theta_pow_prime p hp a b d ha hb n
end CharacteristicP

theorem theta_frobenius_dvd {R : Type*} [CommRing R]
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : R) (d : ℤ)
    (ha : a ^ 2 = (d : R)) (hb : b ^ 2 = (2 : R)) (n : Fin 4 → ℤ) :
    (p : R) ∣ theta a b n ^ p -
      theta ((legendreSym p d : R) * a) ((legendreSym p 2 : R) * b) n := by
  by_cases hu : IsUnit (p : R)
  · exact hu.dvd
  let I : Ideal R := Ideal.span {(p : R)}
  let : CharP (R ⧸ I) p := CharP.quotient R p hu
  let f : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hqa : (f a) ^ 2 = (d : R ⧸ I) := by
    simpa only [map_pow, map_intCast] using congrArg f ha
  have hqb : (f b) ^ 2 = (2 : R ⧸ I) := by
    simpa only [map_pow, map_ofNat] using congrArg f hb
  have ht := theta_pow_prime p hp (f a) (f b) d hqa hqb n
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change f (theta a b n ^ p -
    theta ((legendreSym p d : R) * a) ((legendreSym p 2 : R) * b) n) = 0
  simpa only [map_sub, map_pow, theta, map_add, map_mul, map_intCast, sub_eq_zero] using ht

theorem legendre_two_sign (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = 1 ∨ legendreSym p 2 = -1 := by
  apply legendreSym.eq_one_or_neg_one
  intro hz
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using hz)
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)

theorem theta_frobenius_two_conjugates {R : Type*} [CommRing R]
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : R) (d : ℤ)
    (ha : a ^ 2 = (d : R)) (hb : b ^ 2 = (2 : R))
    (hd : legendreSym p d = -1) :
    (∀ n : Fin 4 → ℤ, (p : R) ∣ theta a b n ^ p - theta (-a) b n) ∨
    (∀ n : Fin 4 → ℤ, (p : R) ∣ theta a b n ^ p - theta (-a) (-b) n) := by
  rcases legendre_two_sign p hp with hpos | hneg
  · left
    intro n
    simpa only [hd, hpos, Int.cast_neg, Int.cast_one, neg_one_mul, one_mul] using
      theta_frobenius_dvd p hp a b d ha hb n
  · right
    intro n
    simpa only [hd, hneg, Int.cast_neg, Int.cast_one, neg_one_mul] using
      theta_frobenius_dvd p hp a b d ha hb n

end Awei.W39



namespace SiegelZerosAwei.W41

open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
variable {K : Type*} [CommRing K]

theorem det_lower_unitriangular_mul (T A : Matrix n n K)
    (hbelow : ∀ i j, i < j → T i j = 0)
    (hdiag : ∀ i, T i i = 1) :
    (T * A).det = A.det := by
  have ht : T.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hbelow i j hij
  rw [Matrix.det_mul, Matrix.det_of_isLowerTriangular T ht]
  simp [hdiag]

theorem exists_lower_unitriangular_of_row_sub_mem_span
    (A B : Matrix n n K)
    (h : ∀ i, B i - A i ∈ Submodule.span K
      (A '' (↑(Finset.univ.filter fun j : n => j < i) : Set n))) :
    ∃ T : Matrix n n K,
      (∀ i j, i < j → T i j = 0) ∧
      (∀ i, T i i = 1) ∧ B = T * A := by
  classical
  have hc : ∀ i, ∃ c : n → K,
      ∑ j ∈ Finset.univ.filter (fun j : n => j < i), c j • A j = B i - A i := by
    intro i
    exact (Submodule.mem_span_image_finset_iff_exists_fun' K).mp (h i)
  choose c hc using hc
  let L : Matrix n n K := fun i j => if j < i then c i j else 0
  have hLA : L * A = B - A := by
    ext i k
    change (∑ j, L i j * A j k) = B i k - A i k
    simpa [L, Finset.sum_filter, Pi.smul_apply,
      smul_eq_mul, ite_mul] using congrFun (hc i) k
  refine ⟨1 + L, ?_, ?_, ?_⟩
  · intro i j hij
    have hji : ¬ j < i := not_lt_of_ge (le_of_lt hij)
    change (1 : Matrix n n K) i j + L i j = 0
    simp [L, ne_of_lt hij, hji]
  · intro i
    change (1 : Matrix n n K) i i + L i i = 1
    simp [L]
  · rw [Matrix.add_mul, Matrix.one_mul, hLA]
    simp [sub_eq_add_neg]

theorem det_eq_of_row_sub_mem_span (A B : Matrix n n K)
    (h : ∀ i, B i - A i ∈ Submodule.span K
      (A '' (↑(Finset.univ.filter fun j : n => j < i) : Set n))) :
    B.det = A.det := by
  obtain ⟨T, ht, hd, hB⟩ := exists_lower_unitriangular_of_row_sub_mem_span A B h
  rw [hB]
  exact det_lower_unitriangular_mul T A ht hd

theorem det_eq_in_integral_ring_of_ambient_row_span
    {R : Type*} [CommRing R] (f : R →+* K) (hf : Function.Injective f)
    (A B : Matrix n n R)
    (h : ∀ i, (B.map f) i - (A.map f) i ∈ Submodule.span K
      ((A.map f) '' (↑(Finset.univ.filter fun j : n => j < i) : Set n))) :
    B.det = A.det := by
  apply hf
  rw [f.map_det, f.map_det]
  exact det_eq_of_row_sub_mem_span (A.map f) (B.map f) h

end SiegelZerosAwei.W41



namespace WeightedTorusJets.W42

open scoped BigOperators

variable {R : Type*} [CommRing R]

def replacementEntry (x y z t : R) (p r k b c : ℕ) : R :=
  x ^ r * (x ^ p - y) ^ k * z ^ b * t ^ c

theorem pow_dvd_replacementEntry (x y z t : R) (p r k b c : ℕ)
    (h : (p : R) ∣ x ^ p - y) :
    (p : R) ^ k ∣ replacementEntry x y z t p r k b c := by
  exact (((pow_dvd_pow_of_dvd h k).mul_left (x ^ r)).mul_right (z ^ b)).mul_right
    (t ^ c)

theorem replacementEntry_mem_principal (x y z t : R) (p r k b c : ℕ)
    (h : x ^ p - y ∈ Ideal.span ({(p : R)} : Set R)) :
    replacementEntry x y z t p r k b c ∈
      Ideal.span ({(p : R) ^ k} : Set R) := by
  apply Ideal.mem_span_singleton.mpr
  exact pow_dvd_replacementEntry x y z t p r k b c (Ideal.mem_span_singleton.mp h)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prod_dvd_det_of_row_dvd (A : Matrix ι ι R) (d : ι → R)
    (h : ∀ i j, d i ∣ A i j) :
    (∏ i, d i) ∣ A.det := by
  classical
  let B : Matrix ι ι R := fun i j => Classical.choose (h i j)
  have hA : A = Matrix.of (fun i j => d i * B i j) := by
    ext i j
    exact Classical.choose_spec (h i j)
  rw [hA, Matrix.det_mul_column]
  exact dvd_mul_right _ _

theorem pow_sum_dvd_det_of_row_dvd (A : Matrix ι ι R) (p : R) (k : ι → ℕ)
    (h : ∀ i j, p ^ k i ∣ A i j) :
    p ^ (∑ i, k i) ∣ A.det := by
  have hd := prod_dvd_det_of_row_dvd A (fun i => p ^ k i) h
  simpa only [Finset.prod_pow_eq_pow_sum] using hd

theorem pow_sum_dvd_replacement_det
    (x y z t : ι → R) (p : ℕ) (r k b c : ι → ℕ)
    (hfrob : ∀ j, (p : R) ∣ x j ^ p - y j) :
    (p : R) ^ (∑ i, k i) ∣
      (Matrix.of fun i j => replacementEntry (x j) (y j) (z j) (t j)
        p (r i) (k i) (b i) (c i)).det := by
  apply pow_sum_dvd_det_of_row_dvd
  intro i j
  exact pow_dvd_replacementEntry (x j) (y j) (z j) (t j)
    p (r i) (k i) (b i) (c i) (hfrob j)

theorem floor_sum_dvd_replacement_det
    (x y z t : ι → R) (p : ℕ) (a b c : ι → ℕ)
    (hfrob : ∀ j, (p : R) ∣ x j ^ p - y j) :
    (p : R) ^ (∑ i, a i / p) ∣
      (Matrix.of fun i j => replacementEntry (x j) (y j) (z j) (t j)
        p (a i % p) (a i / p) (b i) (c i)).det := by
  exact pow_sum_dvd_replacement_det x y z t p
    (fun i => a i % p) (fun i => a i / p) b c hfrob

theorem det_eq_of_map_det_eq {S : Type*} [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (A B : Matrix ι ι R)
    (h : (f.mapMatrix A).det = (f.mapMatrix B).det) : A.det = B.det := by
  apply hf
  simpa only [f.map_det] using h

theorem pow_sum_dvd_det_of_map_det_eq {S : Type*} [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (A B : Matrix ι ι R)
    (hdet : (f.mapMatrix A).det = (f.mapMatrix B).det)
    (p : R) (k : ι → ℕ) (hrow : ∀ i j, p ^ k i ∣ B i j) :
    p ^ (∑ i, k i) ∣ A.det := by
  rw [det_eq_of_map_det_eq f hf A B hdet]
  exact pow_sum_dvd_det_of_row_dvd B p k hrow

end WeightedTorusJets.W42


section

open scoped NumberField
open NumberField

namespace WeightedTorusJets.W43

variable {K : Type*} [Field K] [NumberField K]

theorem integral_norm_cast (x : 𝓞 K) :
    (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K) :=
  Algebra.coe_norm_int x

theorem integral_norm_natCast (p : ℕ) :
    Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ Module.finrank ℚ K := by
  have h := Algebra.norm_algebraMap_of_basis (RingOfIntegers.basis K) (p : ℤ)
  rw [← Module.finrank_eq_card_basis (RingOfIntegers.basis K), RingOfIntegers.rank] at h
  simpa using h

theorem norm_dvd_of_scalar_pow_dvd (p E : ℕ) (Δ : 𝓞 K)
    (hΔ : (p : 𝓞 K) ^ E ∣ Δ) :
    (p : ℤ) ^ (Module.finrank ℚ K * E) ∣ Algebra.norm ℤ Δ := by
  rcases hΔ with ⟨x, rfl⟩
  refine ⟨Algebra.norm ℤ x, ?_⟩
  rw [map_mul, map_pow, integral_norm_natCast, ← pow_mul]

theorem quartic_norm_dvd (hdegree : Module.finrank ℚ K = 4)
    (p E : ℕ) (Δ : 𝓞 K) (hΔ : (p : 𝓞 K) ^ E ∣ Δ) :
    (p : ℤ) ^ (4 * E) ∣ Algebra.norm ℤ Δ := by
  simpa [hdegree] using norm_dvd_of_scalar_pow_dvd p E Δ hΔ

theorem quartic_norm_dvd_of_mem (hdegree : Module.finrank ℚ K = 4)
    (p E : ℕ) (Δ : 𝓞 K)
    (hΔ : Δ ∈ Ideal.span ({(p : 𝓞 K) ^ E} : Set (𝓞 K))) :
    (p : ℤ) ^ (4 * E) ∣ Algebra.norm ℤ Δ :=
  quartic_norm_dvd hdegree p E Δ (Ideal.mem_span_singleton.mp hΔ)

theorem prime_product_dvd_norm (hdegree : Module.finrank ℚ K = 4)
    (S : Finset ℕ) (E : ℕ → ℕ) (Δ : 𝓞 K)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hΔ : ∀ p ∈ S, (p : 𝓞 K) ^ E p ∣ Δ) :
    (∏ p ∈ S, (p : ℤ) ^ (4 * E p)) ∣ Algebra.norm ℤ Δ := by
  apply Finset.prod_dvd_of_coprime
  · intro p hp r hr hpr
    exact ((Nat.coprime_primes (hprime p hp) (hprime r hr)).mpr hpr).isCoprime.pow
  · intro p hp
    exact quartic_norm_dvd hdegree p (E p) Δ (hΔ p hp)

theorem integral_norm_ne_zero (Δ : 𝓞 K) (hΔ : Δ ≠ 0) :
    Algebra.norm ℤ Δ ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr hΔ

end WeightedTorusJets.W43

end


namespace WeightedTorusJets.W45

theorem prime_power_product_dvd (S : Finset ℕ) (E : ℕ → ℕ) (d : ℕ) (z : ℤ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hdiv : ∀ p ∈ S, (p : ℤ) ^ (d * E p) ∣ z) :
    (∏ p ∈ S, (p : ℤ) ^ (d * E p)) ∣ z := by
  apply Finset.prod_dvd_of_coprime
  · intro p hp r hr hpr
    exact ((Nat.coprime_primes (hprime p hp) (hprime r hr)).mpr hpr).isCoprime.pow
  · exact hdiv

theorem weighted_prime_log_le (S : Finset ℕ) (E : ℕ → ℕ) (d : ℕ) (z : ℤ)
    (hz : z ≠ 0) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hdiv : ∀ p ∈ S, (p : ℤ) ^ (d * E p) ∣ z) :
    (d : ℝ) * (∑ p ∈ S, (E p : ℝ) * Real.log p) ≤ Real.log |(z : ℝ)| := by
  have hprod := prime_power_product_dvd S E d z hprime hdiv
  have hnat : (∏ p ∈ S, p ^ (d * E p)) ∣ z.natAbs := by
    apply Int.natCast_dvd.mp
    simpa using hprod
  have hle : (∏ p ∈ S, p ^ (d * E p)) ≤ z.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hnat
  have hreal : (∏ p ∈ S, (p : ℝ) ^ (d * E p)) ≤ |(z : ℝ)| := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hle
    simpa only [Nat.cast_prod, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] using hc
  have hpos : 0 < ∏ p ∈ S, (p : ℝ) ^ (d * E p) := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (by exact_mod_cast (hprime p hp).pos) _
  have hlog := Real.log_le_log hpos hreal
  have hne : ∀ p ∈ S, (p : ℝ) ^ (d * E p) ≠ 0 := by
    intro p hp
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (hprime p hp).ne_zero)
  rw [Real.log_prod (s := S) (f := fun p : ℕ => (p : ℝ) ^ (d * E p)) hne] at hlog
  simp only [Real.log_pow, Nat.cast_mul] at hlog
  simpa only [Finset.mul_sum, mul_assoc] using hlog

theorem weighted_prime_log_le_div_degree (S : Finset ℕ) (E : ℕ → ℕ)
    (d : ℕ) (hd : 0 < d) (z : ℤ) (hz : z ≠ 0)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hdiv : ∀ p ∈ S, (p : ℤ) ^ (d * E p) ∣ z) :
    (∑ p ∈ S, (E p : ℝ) * Real.log p) ≤ Real.log |(z : ℝ)| / d := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  simpa only [mul_comm] using weighted_prime_log_le S E d z hz hprime hdiv

theorem quartic_weighted_prime_log_le (S : Finset ℕ) (E : ℕ → ℕ) (z : ℤ)
    (hz : z ≠ 0) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hdiv : ∀ p ∈ S, (p : ℤ) ^ (4 * E p) ∣ z) :
    (∑ p ∈ S, (E p : ℝ) * Real.log p) ≤ (1 / 4 : ℝ) * Real.log |(z : ℝ)| := by
  have h := weighted_prime_log_le_div_degree S E 4 (by decide) z hz hprime hdiv
  simpa only [Nat.cast_ofNat, div_eq_mul_inv, one_mul, mul_comm] using h

end WeightedTorusJets.W45


section

open scoped NumberField
open NumberField

namespace WeightedTorusJets.W45

variable {K : Type*} [Field K] [NumberField K]

theorem quartic_integral_norm_log_lower
    (hdegree : Module.finrank ℚ K = 4) (S : Finset ℕ) (E : ℕ → ℕ)
    (Δ : 𝓞 K) (hΔ : Δ ≠ 0)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hdiv : ∀ p ∈ S, (p : 𝓞 K) ^ E p ∣ Δ) :
    (∑ p ∈ S, (E p : ℝ) * Real.log p) ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℤ Δ : ℝ)| := by
  apply quartic_weighted_prime_log_le S E (Algebra.norm ℤ Δ)
  · exact W43.integral_norm_ne_zero Δ hΔ
  · exact hprime
  · intro p hp
    exact W43.quartic_norm_dvd hdegree p (E p) Δ (hdiv p hp)

end WeightedTorusJets.W45

end


open scoped BigOperators NumberField

namespace SiegelZerosAwei.W60

open WeightedTorusJets.W40 WeightedTorusJets.W42

variable {ι R K : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [CommRing R] [CommRing K]

def rows (x y z : ι → R) (a b c : ι → ℕ) : Matrix ι ι R :=
  fun i j => rowEntry (x j) (y j) (z j) (a i) (b i) (c i)

def EarlierSpan (f : R →+* K) (H : ℕ) (x y z : ι → R) (a b c : ι → ℕ) : Prop :=
  ∀ i a' b' c', weight H a' b' c' < weight H (a i) (b i) (c i) →
    (fun j => rowEntry (f (x j)) (f (y j)) (f (z j)) a' b' c') ∈
      Submodule.span K (((rows x y z a b c).map f) ''
        (↑(Finset.univ.filter fun j : ι => j < i) : Set ι))

theorem determinant_dvd_second (f : R →+* K) (hf : Function.Injective f)
    (H p : ℕ) (hp : H < p) (x y z : ι → R) (a b c : ι → ℕ)
    (hearlier : EarlierSpan f H x y z a b c)
    (hfrob : ∀ j, (p : R) ∣ x j ^ p - y j) :
    (p : R) ^ (∑ i, a i / p) ∣ (rows x y z a b c).det := by
  let B : Matrix ι ι R := fun i j => replacementEntry (x j) (y j) (y j) (z j)
    p (a i % p) (a i / p) (b i) (c i)
  have hdet : B.det = (rows x y z a b c).det := by
    apply W41.det_eq_in_integral_ring_of_ambient_row_span f hf
    intro i
    have he : p * (a i / p) + a i % p = a i := Nat.div_add_mod (a i) p
    have hexp : (B.map f) i = ((rows x y z a b c).map f) i +
        ∑ m ∈ Finset.range (a i / p), replacementCoefficient (R := K) (a i / p) (m + 1) •
          (fun j => rowEntry (f (x j)) (f (y j)) (f (z j))
            (p * (a i / p - (m + 1)) + a i % p) (b i + (m + 1)) (c i)) := by
      funext j
      change f (B i j) = _
      simpa [B, rows, replacementEntry, rowEntry, he, Pi.add_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        replacement_original_add_lower (f (x j)) (f (y j)) (f (z j))
          p (a i / p) (a i % p) (b i) (c i)
    rw [hexp]
    simp only [add_sub_cancel_left]
    apply Submodule.sum_mem
    intro m hm
    apply Submodule.smul_mem
    apply hearlier
    have hw := replacement_weight_lt_second H p (a i / p) (a i % p)
      (b i) (c i) (m + 1) hp (Nat.succ_pos m)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hm))
    simpa only [he] using hw
  rw [← hdet]
  exact floor_sum_dvd_replacement_det x y y z p a b c hfrob

omit [DecidableEq ι] in
theorem EarlierSpan.swap (f : R →+* K) (H : ℕ) (x y z : ι → R) (a b c : ι → ℕ)
    (h : EarlierSpan f H x y z a b c) : EarlierSpan f H x z y a c b := by
  intro i a' b' c' hw
  have hweight : weight H a' c' b' < weight H (a i) (b i) (c i) := by
    simpa only [weight, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hw
  have hrows : rows x z y a c b = rows x y z a b c := by
    funext j k
    exact mul_right_comm _ _ _
  rw [hrows]
  simpa only [rowEntry, mul_assoc, mul_left_comm, mul_comm] using
    h i a' c' b' hweight

theorem determinant_dvd_either (f : R →+* K) (hf : Function.Injective f)
    (H p : ℕ) (hp : H < p) (x y z : ι → R) (a b c : ι → ℕ)
    (hearlier : EarlierSpan f H x y z a b c)
    (hfrob : (∀ j, (p : R) ∣ x j ^ p - y j) ∨
      (∀ j, (p : R) ∣ x j ^ p - z j)) :
    (p : R) ^ (∑ i, a i / p) ∣ (rows x y z a b c).det := by
  rcases hfrob with hy | hz
  · exact determinant_dvd_second f hf H p hp x y z a b c hearlier hy
  · have h := determinant_dvd_second f hf H p hp x z y a c b
      (EarlierSpan.swap f H x y z a b c hearlier) hz
    have hrows : rows x z y a c b = rows x y z a b c := by
      funext j k
      exact mul_right_comm _ _ _
    simpa only [hrows] using h

theorem theta_determinant_dvd (f : R →+* K) (hf : Function.Injective f)
    (H p : ℕ) [Fact p.Prime] (hpH : H < p) (hp2 : p ≠ 2)
    (u v : R) (d : ℤ) (hu : u ^ 2 = (d : R)) (hv : v ^ 2 = 2)
    (hd : legendreSym p d = -1) (n : ι → Fin 4 → ℤ) (a b c : ι → ℕ)
    (hearlier : EarlierSpan f H (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j)) a b c) :
    (p : R) ^ (∑ i, a i / p) ∣
      (rows (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j)) a b c).det := by
  apply determinant_dvd_either f hf H p hpH _ _ _ a b c hearlier
  rcases Awei.W39.theta_frobenius_two_conjugates p hp2 u v d hu hv hd with h | h
  · exact Or.inl (fun j => h (n j))
  · exact Or.inr (fun j => h (n j))

variable {L : Type*} [Field L] [NumberField L]

theorem theta_integer_norm_dvd
    (H p : ℕ) [Fact p.Prime] (hpH : H < p) (hp2 : p ≠ 2)
    (u v : 𝓞 L) (d : ℤ) (hu : u ^ 2 = (d : 𝓞 L)) (hv : v ^ 2 = 2)
    (hd : legendreSym p d = -1) (n : ι → Fin 4 → ℤ) (a b c : ι → ℕ)
    (hearlier : EarlierSpan (algebraMap (𝓞 L) L) H
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j)) a b c) :
    (p : ℤ) ^ (Module.finrank ℚ L * (∑ i, a i / p)) ∣
      Algebra.norm ℤ
        (rows (fun j => Awei.W39.theta u v (n j))
          (fun j => Awei.W39.theta (-u) v (n j))
          (fun j => Awei.W39.theta (-u) (-v) (n j)) a b c).det := by
  apply WeightedTorusJets.W43.norm_dvd_of_scalar_pow_dvd
  exact theta_determinant_dvd (algebraMap (𝓞 L) L)
    NumberField.RingOfIntegers.coe_injective H p hpH hp2 u v d hu hv hd n a b c hearlier


end SiegelZerosAwei.W60


end SiegelZeros

end OAI
