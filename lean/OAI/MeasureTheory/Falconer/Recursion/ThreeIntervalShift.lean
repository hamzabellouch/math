import OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalPower
import OAI.MeasureTheory.Falconer.Radial.OuterRadialWidths

namespace OAI

/-! # The three-interval gain with a fixed coarsening of the middle radial scale -/

namespace Falconer

theorem three_interval_shifted_power {a b N J : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    (hJ : J ≤ b-a) {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    ((2:ℝ)^N)^(20*η+3*ξ)*((2:ℝ)^a)^(-q)*
      (1/(2:ℝ)^((b-a)-J))^(q+c)*((2:ℝ)^(N-b))^(-q) ≤
        ((2:ℝ)^N)^(-q-γ) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hmid : (1/(2:ℝ)^((b-a)-J))^(q+c) =
      ((2:ℝ)^J)^(q+c)*((2:ℝ)^(b-a))^(-q-c) := by
    rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
    have hh := dyadic_shifted_decay (g := 0) (v := b-a) (by simpa using hJ) (q+c)
    simpa only [Nat.sub_zero,zero_add,neg_add_rev,sub_eq_add_neg,add_comm] using hh
  rw [hmid]
  calc
    _ ≤ ((2:ℝ)^N)^(20*η+3*ξ)*((2:ℝ)^a)^(-q)*
        (((2:ℝ)^N)^ξ*((2:ℝ)^(b-a))^(-q-c))*((2:ℝ)^(N-b))^(-q) := by
      gcongr
    _ = ((2:ℝ)^N)^(10*η+(10*η+ξ)+3*ξ)*((2:ℝ)^a)^(-q)*
        ((2:ℝ)^(b-a))^(-q-c)*((2:ℝ)^(N-b))^(-q) := by
      conv_rhs => rw [show 10*η+(10*η+ξ)+3*ξ = (20*η+3*ξ)+ξ by ring,Real.rpow_add hR]
      ring
    _ ≤ _ := three_interval_radial_power a (b-a) (N-b) N (by omega) hc hwidth (by linarith)

theorem three_interval_relative_budget {L τ Δ gain γ : ℝ}
    (hΔ : 0 ≤ Δ) (hγ : γ ≤ Δ) (hgain : 0 ≤ gain)
    (hsmall : (20*L+4)*τ ≤ gain/8) :
    20*(L*τ*Δ)+4*(τ*Δ)+(gain*γ/8) ≤ (gain/2)*(Δ/2) := by
  have hscaled := mul_le_mul_of_nonneg_right hsmall hΔ
  have hmargin := mul_le_mul_of_nonneg_left hγ hgain
  nlinarith

end Falconer

end OAI
