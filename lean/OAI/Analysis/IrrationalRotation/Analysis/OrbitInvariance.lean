import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

namespace OAI

namespace Invariant233.OrbitInvariance

section Ring
variable {A : Type*} [Ring A] {p T : A}

theorem invariant_iff_compression :
    (1 - p) * T * p = 0 ↔ p * T * p = T * p := by
  rw [sub_mul, one_mul, sub_mul]
  exact sub_eq_zero.trans eq_comm

theorem invariant_pow (hp : IsIdempotentElem p)
    (hT : (1 - p) * T * p = 0) (n : ℕ) :
    (1 - p) * T ^ n * p = 0 := by
  have hTp : p * T * p = T * p := invariant_iff_compression.mp hT
  apply invariant_iff_compression.mpr
  induction n with
  | zero => simpa using hp.eq
  | succ n ih =>
    calc
      p * T ^ (n + 1) * p = p * T ^ n * (T * p) := by rw [pow_succ]; simp [mul_assoc]
      _ = p * T ^ n * (p * T * p) := by rw [hTp]
      _ = (p * T ^ n * p) * T * p := by simp [mul_assoc]
      _ = (T ^ n * p) * T * p := by rw [ih]
      _ = T ^ n * (p * T * p) := by simp [mul_assoc]
      _ = T ^ n * (T * p) := by rw [hTp]
      _ = T ^ (n + 1) * p := by rw [pow_succ]; simp [mul_assoc]

theorem orbit_inclusion (W : Aˣ) (D : A)
    (h : (1 - p) * ((W : A) * D) * p = 0) :
    (1 - (↑(W⁻¹) * p * (W : A))) * D * p = 0 := by
  have heq : ↑(W⁻¹) * ((1 - p) * ((W : A) * D) * p) =
      (1 - (↑(W⁻¹) * p * (W : A))) * D * p := by
    simp only [mul_sub, sub_mul, one_mul, mul_assoc]
    simp
  rw [← heq, h, mul_zero]

theorem orbit_inclusion_pow (hp : IsIdempotentElem p)
    (hT : (1 - p) * T * p = 0) (n : ℕ) (W : Aˣ) (D : A)
    (hfactor : T ^ n = (W : A) * D) :
    (1 - (↑(W⁻¹) * p * (W : A))) * D * p = 0 := by
  apply orbit_inclusion W D
  rw [← hfactor]
  exact invariant_pow hp hT n

theorem endpoint_inclusion_pow {q D : A} (hq : IsIdempotentElem q)
    (hT : (1 - q) * T * q = 0) (hD : (1 - q) * D * p = 0) (n : ℕ) :
    (1 - q) * T ^ n * D * p = 0 := by
  have hD' : q * (D * p) = D * p := by
    rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at hD
    simpa only [mul_assoc] using hD.symm
  calc
    (1 - q) * T ^ n * D * p = ((1 - q) * T ^ n) * (D * p) := by
      simp only [mul_assoc]
    _ = ((1 - q) * T ^ n) * (q * (D * p)) := by rw [hD']
    _ = ((1 - q) * T ^ n * q) * (D * p) := by simp only [mul_assoc]
    _ = 0 := by rw [invariant_pow hq hT n, zero_mul]

end Ring

section Algebra
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {p T : A}

theorem invariant_smul_iff {c : 𝕜} (hc : c ≠ 0) :
    (1 - p) * (c • T) * p = 0 ↔ (1 - p) * T * p = 0 := by
  rw [mul_smul_comm, smul_mul_assoc, smul_eq_zero]
  exact or_iff_right hc

theorem orbit_inclusion_normalized (W : Aˣ) (D : A) {c : 𝕜}
    (h : (1 - p) * ((W : A) * D) * p = 0) :
    (1 - (↑(W⁻¹) * p * (W : A))) * (c⁻¹ • D) * p = 0 := by
  rw [mul_smul_comm, smul_mul_assoc, orbit_inclusion W D h, smul_zero]

end Algebra

section WeightedPowers
variable {B A : Type*} [CommRing B] [Ring A]
variable (π : B →+* A) (σ : B →+* B) (U : A)
variable (hcov : ∀ b : B, π b * U = U * π (σ b))
include hcov

theorem covariance_pow (b : B) (n : ℕ) :
    π b * U ^ n = U ^ n * π ((σ : B → B)^[n] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      π b * U ^ (n + 1) = (π b * U ^ n) * U := by rw [pow_succ, mul_assoc]
      _ = (U ^ n * π ((σ : B → B)^[n] b)) * U := by rw [ih]
      _ = U ^ n * (π ((σ : B → B)^[n] b) * U) := by rw [mul_assoc]
      _ = U ^ n * (U * π (σ ((σ : B → B)^[n] b))) := by rw [hcov]
      _ = U ^ (n + 1) * π ((σ : B → B)^[n + 1] b) := by
        rw [pow_succ, Function.iterate_succ_apply', mul_assoc]

theorem weighted_pow (f : B) (n : ℕ) :
    (U * π f) ^ n = U ^ n * π (∏ k ∈ Finset.range n, (σ : B → B)^[k] f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih]
    calc
      U * π f * (U ^ n * π (∏ k ∈ Finset.range n, (σ : B → B)^[k] f)) =
          U * (π f * U ^ n) * π (∏ k ∈ Finset.range n, (σ : B → B)^[k] f) := by
            simp only [mul_assoc]
      _ = U * (U ^ n * π ((σ : B → B)^[n] f)) *
          π (∏ k ∈ Finset.range n, (σ : B → B)^[k] f) := by
            rw [covariance_pow π σ U hcov f n]
      _ = U ^ (n + 1) * π ((σ : B → B)^[n] f *
          ∏ k ∈ Finset.range n, (σ : B → B)^[k] f) := by
            rw [map_mul, pow_succ']; simp only [mul_assoc]
      _ = U ^ (n + 1) * π (∏ k ∈ Finset.range (n + 1), (σ : B → B)^[k] f) := by
            rw [Finset.prod_range_succ, mul_comm ((σ : B → B)^[n] f)]

end WeightedPowers

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p T : E →L[𝕜] E}

theorem invariant_iff_mapsTo_range (hp : IsIdempotentElem p) :
    (1 - p) * T * p = 0 ↔ Set.MapsTo T (p.range : Set E) (p.range : Set E) := by
  rw [invariant_iff_compression]
  constructor
  · intro h x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨T (p y), ?_⟩
    exact congrArg (fun A : E →L[𝕜] E => A y) h
  · intro h
    ext x
    rcases h (show p x ∈ p.range from ⟨x, rfl⟩) with ⟨y, hy⟩
    change p (T (p x)) = T (p x)
    rw [← hy]
    exact congrArg (fun A : E →L[𝕜] E => A y) hp.eq

theorem mapsTo_range_pow (hp : IsIdempotentElem p)
    (hT : Set.MapsTo T (p.range : Set E) (p.range : Set E)) (n : ℕ) :
    Set.MapsTo (T ^ n) (p.range : Set E) (p.range : Set E) := by
  exact (invariant_iff_mapsTo_range hp).mp
    (invariant_pow hp ((invariant_iff_mapsTo_range hp).mpr hT) n)


end Invariant233.OrbitInvariance

end OAI
