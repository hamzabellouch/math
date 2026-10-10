import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylBlocks
import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylDifference

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset

theorem quadratic_weyl_rational_bound (alpha beta start : ℝ) (N : ℕ)
    (b : ℤ) (r : ℕ) (hr : 0 < r) (hcop : Int.gcd (r:ℤ) b = 1)
    (happrox : |2*alpha-(b:ℝ)/r| ≤ 1/(r:ℝ)^2)
    (hrM : (r:ℝ) ≤ (N+1:ℝ)^2) :
    ‖quadraticWeylSum alpha beta start (N+1)‖^2 ≤
      32*(1+Real.log (N+1:ℝ))*((N+1:ℝ)^2/r+(N+1:ℝ)+r) := by
  let u : ℕ → ℝ := fun h => ‖∑ i ∈ range (N-h), weylPhase ((i:ℝ)*(2*alpha*(h+1)))‖
  have huN : ∀ h ∈ range N, u h ≤ N := by
    intro h hh
    exact (linear_weyl_bound (2*alpha*(h+1)) (N-h)).1.trans
      (by exact_mod_cast Nat.sub_le N h)
  have hsum := rational_block_sum_bound (2*alpha) b r N hr hcop happrox u
    (fun _ _ => norm_nonneg _) huN
    (fun h _ => (linear_weyl_bound (2*alpha*(h+1)) (N-h)).2)
  have hdiff := quadratic_weyl_differencing alpha beta start N
  have hfirst : ‖quadraticWeylSum alpha beta start (N+1)‖^2 ≤
      (N+1:ℝ)+2*((2*(N:ℝ)/r+1)*(2*(N:ℝ)+2*(r:ℝ)*(harmonic r:ℝ))) := by
    change _ ≤ (N+1:ℝ)+2*∑ h ∈ range N, u h at hdiff
    linarith only [hdiff,hsum]
  let M : ℝ := N+1
  let H : ℝ := 1+Real.log M
  have hM : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hMp : 0 < M := by linarith
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hM]
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hhar : (harmonic r:ℝ) ≤ 2*H := by
    have h1 := harmonic_le_one_add_log r
    have h2 := Real.log_le_log hrp hrM
    rw [Real.log_pow] at h2
    dsimp [H,M]
    norm_num at h2
    exact h1.trans (by linarith)
  have hfac : 2*(N:ℝ)/r+1 ≤ 2*M/r+1 := by
    dsimp [M]
    gcongr; linarith
  have hbody : 2*(N:ℝ)+2*(r:ℝ)*(harmonic r:ℝ) ≤ 2*M+4*(r:ℝ)*H := by
    have hh := mul_le_mul_of_nonneg_left hhar (show 0 ≤ 2*(r:ℝ) by positivity)
    dsimp [M]
    linarith only [hh]
  have hhar0 : (0:ℝ) ≤ (harmonic r:ℝ) := by
    unfold harmonic
    positivity
  have hprod := mul_le_mul hfac hbody (by positivity)
    (show 0 ≤ 2*M/r+1 by positivity)
  have he : M+2*((2*M/r+1)*(2*M+4*(r:ℝ)*H)) =
      8*M^2/r+5*M+16*M*H+8*(r:ℝ)*H := by field_simp; ring
  have hq : 0 ≤ M^2/(r:ℝ) := by positivity
  have hquad := mul_le_mul_of_nonneg_right hH hq
  have hlin := mul_le_mul_of_nonneg_right hH hMp.le
  have hRH : 0 ≤ (r:ℝ)*H := by positivity
  change _ ≤ 32*H*(M^2/r+M+r)
  calc
    _ ≤ M+2*((2*M/r+1)*(2*M+4*(r:ℝ)*H)) := by
      change _ ≤ M+2*((2*(N:ℝ)/r+1)*(2*(N:ℝ)+2*(r:ℝ)*(harmonic r:ℝ))) at hfirst
      linarith only [hfirst,hprod]
    _ = 8*M^2/r+5*M+16*M*H+8*(r:ℝ)*H := he
    _ ≤ _ := by
      simp only [div_eq_mul_inv] at hquad hq ⊢
      nlinarith only [hquad,hlin,hq,hRH, mul_nonneg hMp.le (show 0 ≤ H by linarith)]

end Ostmann.QuadraticCenter

end OAI
