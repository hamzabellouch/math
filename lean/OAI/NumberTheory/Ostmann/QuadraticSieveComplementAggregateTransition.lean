import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateKernels

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem complementLargeScalar_support {M T : ℝ} {Δ r d v : ℕ}
    (hM : 0 < M) (hT : 1 ≤ T) (hv : 0 < v)
    (hg : complementLargeScalar M T Δ r d v ≠ 0) :
    complementWindowLower M T v < (r*d:ℕ) := by
  classical
  have hs : Nat.Coprime v Δ ∧ complementWindowUpper M T v < (r*d:ℕ) := by
    by_contra hh
    exact hg (by simp only [complementLargeScalar,ite_eq_right hh])
  have hw := complementary_dyadic_window_parameters hM hT hv
  exact (hw.2.1.trans hw.2.2.1).trans_lt hs.2

theorem complementFourierScalar_support (W : 𝓢(ℝ,ℂ)) {M T : ℝ} {Δ r d v : ℕ}
    (hg : complementFourierScalar W M T Δ r d v ≠ 0) :
    complementWindowLower M T v < (r*d:ℕ) := by
  classical
  by_contra hh
  apply hg
  unfold complementFourierScalar
  exact ite_eq_right (fun h => hh h.2.1)

theorem complement_block_transition {M T : ℝ} {Δ K j r d D v : ℕ}
    (hT : 1 ≤ T) (hΔ : 0 < Δ) (hr : r ∈ (2*Δ).divisors)
    (hv : v ∈ binarySquarefreeRows K j) (hd : d ≤ 2*D)
    (hactive : complementWindowLower M T v < (r*d:ℕ)) :
    Real.sqrt (M/(2^j:ℕ))/(32*(Δ:ℝ)*T) ≤ (D:ℝ)/4 := by
  have hTp : 0 < T := by linarith
  have hΔp : (0:ℝ) < Δ := by exact_mod_cast hΔ
  have hrle : r ≤ 2*Δ := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hr).1
  have hrd : (r:ℝ)*d ≤ 4*(Δ:ℝ)*D := by
    have hn := Nat.mul_le_mul hrle hd
    have hh : (r:ℝ)*d ≤ ((2*Δ:ℕ):ℝ)*((2*D:ℕ):ℝ) := by exact_mod_cast hn
    push_cast at hh
    nlinarith
  unfold complementWindowLower at hactive
  rw [squarefreeDyadicBase_eq_of_mem hv] at hactive
  have hh := (div_lt_iff₀ (show 0 < 2*T by positivity)).mp hactive
  push_cast at hh
  apply (div_le_iff₀ (show 0 < 32*(Δ:ℝ)*T by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hrd (show 0 ≤ 2*T by positivity)
  push_cast
  nlinarith

theorem complement_boundary_transition {M T : ℝ} {Δ K j r v : ℕ}
    (hT : 1 ≤ T) (hΔ : 0 < Δ) (hr : r ∈ (2*Δ).divisors)
    (hv : v ∈ binarySquarefreeRows K j)
    (hactive : complementWindowLower M T v < (r*1:ℕ)) :
    Real.sqrt (M/(2^j:ℕ)) ≤ 4*(Δ:ℝ)*T := by
  have hTp : 0 < T := by linarith
  have hrle : r ≤ 2*Δ := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hr).1
  have hrr : (r:ℝ) ≤ 2*(Δ:ℝ) := by exact_mod_cast hrle
  unfold complementWindowLower at hactive
  rw [squarefreeDyadicBase_eq_of_mem hv] at hactive
  have hh := (div_lt_iff₀ (show 0 < 2*T by positivity)).mp hactive
  push_cast at hh
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hrr hTp.le]

end Ostmann.QuadraticSieve

end

end OAI
