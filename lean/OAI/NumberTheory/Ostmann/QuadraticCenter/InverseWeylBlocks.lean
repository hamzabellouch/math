import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylBins
import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylBlockSpacing

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset

theorem rational_block_sum_bound (theta : ℝ) (b : ℤ) (r N : ℕ) (hr : 0 < r)
    (hcop : Int.gcd (r:ℤ) b = 1)
    (happrox : |theta-(b:ℝ)/r| ≤ 1/(r:ℝ)^2)
    (u : ℕ → ℝ) (hu : ∀ h ∈ range N, 0 ≤ u h)
    (huN : ∀ h ∈ range N, u h ≤ N)
    (hud : ∀ h ∈ range N, u h*integerDistance (theta*(h+1)) ≤ 1/2) :
    ∑ h ∈ range N, u h ≤
      (2*(N:ℝ)/r+1)*(2*(N:ℝ)+2*(r:ℝ)*(harmonic r:ℝ)) := by
  classical
  let L := r/2+1
  have hL : 0 < L := by dsimp [L]; omega
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hmap : ∀ h ∈ range N, h/L ∈ range (N/L+1) := by
    intro h hh
    apply mem_range.mpr
    have : h/L ≤ N/L := Nat.div_le_div_right (Nat.le_of_lt (mem_range.mp hh))
    omega
  have hblock (k : ℕ) :
      ∑ h ∈ (range N).filter (fun h => h/L=k), u h ≤
        2*(N:ℝ)+2*(r:ℝ)*(harmonic r:ℝ) := by
    apply separated_linear_sum_bound _ (fun h : ℕ => theta*((h:ℝ)+1)) u hr (Nat.cast_nonneg N)
    · intro i hi j hj hij m
      obtain ⟨hiN,hik⟩ := mem_filter.mp hi
      obtain ⟨hjN,hjk⟩ := mem_filter.mp hj
      have hquot : i/(r/2+1)=j/(r/2+1) := hik.trans hjk.symm
      exact rational_block_spacing theta b r hr hcop happrox i j hij hquot m
    · intro i hi
      exact hu i (mem_filter.mp hi).1
    · intro i hi
      exact huN i (mem_filter.mp hi).1
    · intro i hi
      exact hud i (mem_filter.mp hi).1
  have hfac : ((N/L+1:ℕ):ℝ) ≤ 2*(N:ℝ)/r+1 := by
    have hdiv : N/L*L ≤ N := Nat.div_mul_le_self N L
    have hdivR : ((N/L:ℕ):ℝ)*(L:ℝ) ≤ N := by exact_mod_cast hdiv
    have hrL : (r:ℝ) ≤ 2*(L:ℝ) := by exact_mod_cast (show r ≤ 2*L by dsimp [L]; omega)
    have hp : 0 ≤ ((N/L:ℕ):ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hrL hp
    have h : ((N/L:ℕ):ℝ) ≤ 2*(N:ℝ)/r := (le_div_iff₀ hrp).mpr (by nlinarith)
    push_cast
    linarith
  have hharm : (0:ℝ) ≤ (harmonic r:ℝ) := by
    exact_mod_cast (show (0:ℚ) ≤ harmonic r by
      unfold harmonic
      exact sum_nonneg (fun _ _ => by positivity))
  have hweight : 0 ≤ 2*(N:ℝ)+2*(r:ℝ)*(harmonic r:ℝ) := by
    positivity
  calc
    _ = ∑ k ∈ range (N/L+1), ∑ h ∈ (range N).filter (fun h => h/L=k), u h :=
      (sum_fiberwise_of_maps_to hmap u).symm
    _ ≤ ∑ _k ∈ range (N/L+1), (2*(N:ℝ)+2*(r:ℝ)*(harmonic r:ℝ)) :=
      sum_le_sum (fun k _ => hblock k)
    _ = ((N/L+1:ℕ):ℝ)*(2*(N:ℝ)+2*(r:ℝ)*(harmonic r:ℝ)) := by simp only [sum_const, card_range, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac hweight

end Ostmann.QuadraticCenter

end OAI
