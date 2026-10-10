import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem recursion_geometric_mean_bound {x N d₁ d₂ t r s : ℝ}
    (hx : 0 ≤ x) (hN : 0 ≤ N) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hfirst : t^2 ≤ r^2) (hcross : t^2*N ≤ r*s)
    (hlast : t^2*N^2 ≤ s^2*(d₁*d₂)) :
    t*Real.sqrt ((x+N/d₁)*(x+N/d₂)) ≤ r*x+s := by
  have hd₁p : 0 < d₁ := by linarith
  have hd₂p : 0 < d₂ := by linarith
  have hP : 0 < d₁*d₂ := mul_pos hd₁p hd₂p
  have hquot₁ : N/d₁ ≤ N := (div_le_self hN hd₁)
  have hquot₂ : N/d₂ ≤ N := (div_le_self hN hd₂)
  have hprod : (x+N/d₁)*(x+N/d₂) ≤ x^2+2*x*N+N^2/(d₁*d₂) := by
    have h₁ := mul_le_mul_of_nonneg_left hquot₁ hx
    have h₂ := mul_le_mul_of_nonneg_left hquot₂ hx
    have hid : (x+N/d₁)*(x+N/d₂) = x^2+x*(N/d₁)+x*(N/d₂)+N^2/(d₁*d₂) := by
      field_simp
      ring
    rw [hid]
    nlinarith
  have h₁ := mul_le_mul_of_nonneg_right hfirst (sq_nonneg x)
  have h₂ := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2*x by positivity)
  have h₃ : t^2*N^2/(d₁*d₂) ≤ s^2 := (div_le_iff₀ hP).mpr hlast
  have hsq : (t*Real.sqrt ((x+N/d₁)*(x+N/d₂)))^2 ≤ (r*x+s)^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    calc
      _ ≤ t^2*(x^2+2*x*N+N^2/(d₁*d₂)) :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg t)
      _ = t^2*x^2+2*x*(t^2*N)+t^2*N^2/(d₁*d₂) := by ring
      _ ≤ r^2*x^2+2*x*(r*s)+s^2 := add_le_add (add_le_add h₁ h₂) h₃
      _ = _ := by ring
  have htarget : 0 ≤ r*x+s := by positivity
  nlinarith

theorem recursion_E4 {M N B x d₁ d₂ Δ : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hx : 0 ≤ x)
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hΔ : 1 ≤ Δ)
    (htransition : Real.sqrt (M/B)/Δ ≤ d₁*d₂) :
    Real.sqrt (M/(B*(d₁*d₂)))*Real.sqrt ((x+N/d₁)*(x+N/d₂)) ≤
      Real.sqrt (M/B)*x+Δ*N := by
  let P := d₁*d₂
  let r := Real.sqrt (M/B)
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le hd₁ hd₂
  have hPp : 0 < P := by linarith
  have hΔp : 0 < Δ := by linarith
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = M/B := Real.sq_sqrt (by positivity)
  have ht2 : (Real.sqrt (M/(B*P)))^2 = r^2/P := by
    rw [Real.sq_sqrt (by positivity),hr2]
    ring
  have htrans : r/P ≤ Δ := by
    apply (div_le_iff₀ hPp).mpr
    have hh := (div_le_iff₀ hΔp).mp htransition
    simpa [r,P,mul_comm] using hh
  apply recursion_geometric_mean_bound hx hN.le hd₁ hd₂ hr (by positivity)
  · rw [ht2]
    exact div_le_self (sq_nonneg r) hP
  · rw [ht2]
    have hh := mul_le_mul_of_nonneg_left htrans hr
    calc
      (r^2/P)*N = (r*(r/P))*N := by ring
      _ ≤ (r*Δ)*N := mul_le_mul_of_nonneg_right hh hN.le
      _ = _ := by ring
  · rw [ht2]
    have hh := pow_le_pow_left₀ (div_nonneg hr hPp.le) htrans 2
    have hhh := mul_le_mul_of_nonneg_right hh (show 0 ≤ N^2*P by positivity)
    calc
      (r^2/P)*N^2 = (r/P)^2*(N^2*P) := by field_simp
      _ ≤ Δ^2*(N^2*P) := hhh
      _ = _ := by dsimp [P]; ring

end Ostmann.QuadraticSieve

end

end OAI
