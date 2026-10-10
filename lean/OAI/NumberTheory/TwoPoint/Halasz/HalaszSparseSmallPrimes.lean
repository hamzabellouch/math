import OAI.NumberTheory.TwoPoint.Halasz.HalaszPublishedPrime
import Mathlib.NumberTheory.Chebyshev

namespace OAI

/-! The small-prime range of the published sparse estimate follows from
Chebyshev and finite weighted Gram duality. Only larger log Y requires
the oscillatory prime estimate. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_dyadic_prime_log_mass {Y : ℝ} (hY : 2 ≤ Y)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) :
    (∑ p ∈ P, Real.log (p:ℝ)) ≤ (2*Real.log 4)*Y := by
  have hsub : P ⊆ (Icc 0 ⌊2*Y⌋₊).filter Nat.Prime := by
    intro p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,
      (Nat.le_floor_iff (by linarith : 0 ≤ 2*Y)).mpr (hP p hp).2.2⟩,(hP p hp).1⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p:ℝ)) hsub
    (fun p hp _ => Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
  have ht := Chebyshev.theta_le_log4_mul_x (by linarith : 0 ≤ 2*Y)
  rw [Chebyshev.theta_eq_sum_Icc] at ht
  exact hs.trans (by convert ht using 1; ring)

theorem halasz_sparse_prime_card_bound {Y : ℝ} (hY : 2 ≤ Y)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y)
    (a : ℕ → ℂ) (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖^2) ≤
      (2*Real.log 4)*(S.card:ℝ)*Y*(∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ)) := by
  let D := ∑ p ∈ P, Real.log (p:ℝ)
  have hlog (p : ℕ) (hp : p ∈ P) : 0 < Real.log (p:ℝ) :=
    Real.log_pos (by exact_mod_cast (hP p hp).1.one_lt)
  have hD : 0 ≤ D := sum_nonneg (fun p hp => (hlog p hp).le)
  have hkernel (t s : ℝ) :
      ‖mrtExponentialPolynomial P (fun p => (Real.log (p:ℝ):ℂ))
        (fun p => -Real.log (p:ℝ)) (t-s)‖ ≤ D := by
    unfold mrtExponentialPolynomial
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro p hp
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hlog p hp),
      Complex.norm_exp_ofReal_mul_I,mul_one,le_refl]
  have hh := mrt_sparse_divided_weight_energy P P (Subset.refl _) (fun p => Real.log (p:ℝ))
    (fun p => -Real.log (p:ℝ)) a (fun p hp => (hlog p hp).le) hlog S hsep
    (show (0:ℝ) ≤ 0 by rfl) hD (fun t _ s _ => by simpa using hkernel t s)
  simp only [mul_zero,zero_add] at hh
  have hm : 0 ≤ ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ) :=
    sum_nonneg (fun p hp => div_nonneg (sq_nonneg _) (hlog p hp).le)
  calc
    _ ≤ ((S.card:ℝ)*D)*(∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ)) := hh
    _ ≤ ((S.card:ℝ)*((2*Real.log 4)*Y))*(∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (halasz_dyadic_prime_log_mass hY P hP) (Nat.cast_nonneg _)) hm
    _ = _ := by ring

lemma halasz_sparse_small_scale {L Y : ℝ} (hL : 1 ≤ L)
    (hY : Real.log Y ≤ 2*L^(3/4:ℝ)*Real.log L) :
    1 ≤ Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2 := by
  have hL0 : 0 < L := by linarith
  have hp : 0 < L^(3/4:ℝ) := Real.rpow_pos_of_pos hL0 _
  have hy : Real.log Y/L^(3/4:ℝ) ≤ 2*Real.log L := by
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hY]
  have he : 1 ≤ Real.exp (-Real.log Y/L^(3/4:ℝ)+2*Real.log L) :=
    Real.one_le_exp_iff.mpr (by rw [neg_div]; linarith only [hy])
  have hs : Real.exp (2*Real.log L) = L^2 := by
    rw [show 2*Real.log L=Real.log L+Real.log L by ring,Real.exp_add,Real.exp_log hL0]
    ring
  rwa [Real.exp_add,hs] at he

/-- This is the exact sparse-input inequality in the small log Y range. -/
theorem halasz_sparse_small_primes {L Y : ℝ} (hL : 1 ≤ L) (hY : 2 ≤ Y)
    (hscale : Real.log Y ≤ 2*L^(3/4:ℝ)*Real.log L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y)
    (a : ℕ → ℂ) (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖^2) ≤
      (2*Real.log 4)*(Y+(S.card:ℝ)*Y*Real.exp (-Real.log Y/L^(3/4:ℝ))*L^2)*
        ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ) := by
  apply (halasz_sparse_prime_card_bound hY P hP a S hsep).trans
  have hm : 0 ≤ ∑ p ∈ P, ‖a p‖^2/Real.log (p:ℝ) := sum_nonneg (fun p hp =>
    div_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le)))
  have hfactor := mul_le_mul_of_nonneg_left (halasz_sparse_small_scale hL hscale)
    (show 0 ≤ (S.card:ℝ)*Y by positivity)
  apply mul_le_mul_of_nonneg_right _ hm
  have hlog : 0 ≤ 2*Real.log 4 := by positivity
  have hy0 : 0 ≤ Y := by linarith
  nlinarith only [hfactor,hlog,hy0]

end TwoPointCorrelations

end OAI
