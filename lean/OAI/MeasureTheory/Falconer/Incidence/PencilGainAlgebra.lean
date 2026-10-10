import OAI.MeasureTheory.Falconer.Geometry.NormalizedGainBudget

namespace OAI

/-! The explicit pencil-size dichotomy behind the normalized regular gain. -/
namespace Falconer

theorem small_pencil_gain_bound {δ Δ s γ η E m : ℝ} (hδ : 0 < δ)
    (hΔ : 0 < Δ) (he : δ = Δ^2)
    (hbudget : δ^(-(γ+η)) ≤ E) (hm : m ≤ 1/δ^(s+γ)) :
    m/δ^(s+η) ≤ E/(Δ^s)^4 := by
  have hden : (Δ^s)^4 = δ^(2*s) := by
    rw [he,← Real.rpow_mul_natCast hΔ.le s 4,← Real.rpow_natCast_mul hΔ.le 2 (2*s)]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hinv (a : ℝ) : 1/δ^a = δ^(-a) := by
    rw [Real.rpow_neg hδ.le,one_div]
  calc
    _ ≤ (1/δ^(s+γ))/δ^(s+η) := div_le_div_of_nonneg_right hm (by positivity)
    _ = δ^(-(γ+η))/δ^(2*s) := by
      rw [div_eq_mul_one_div,hinv,hinv,div_eq_mul_one_div,hinv,
        ← Real.rpow_add hδ,← Real.rpow_add hδ]
      congr 1
      ring
    _ ≤ E/δ^(2*s) := div_le_div_of_nonneg_right hbudget (by positivity)
    _ = _ := by rw [hden]

theorem large_pencil_gain_contradiction {δ κ s γ η A K m U : ℝ}
    (hδ : 0 < δ) (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hm : 0 < m)
    (hrel : γ*(κ/2) = 4*η) (hbudget : 2*A*K^3 ≤ δ^(-3*η))
    (hlarge : 1/δ^(s+γ) ≤ m)
    (hgrowth : m*m^(κ/2) ≤ U*(A*K^3*δ^(s*(1-κ/2)))) :
    ¬ U ≤ m/δ^(s+η) := by
  intro hsmall
  have hcost : A*K^3*δ^(s*(1-κ/2))/δ^(s+η) ≤
      (1/2)*δ^(-(s+γ)*(κ/2)) := by
    calc
      _ = (A*K^3)*δ^(s*(1-κ/2)-(s+η)) := by
        rw [Real.rpow_sub hδ]
        ring
      _ ≤ (δ^(-3*η)/2)*δ^(s*(1-κ/2)-(s+η)) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hbudget]) (by positivity)
      _ = (1/2)*δ^(-3*η+(s*(1-κ/2)-(s+η))) := by
        rw [Real.rpow_add hδ]
        ring
      _ = _ := by congr 2; nlinarith only [hrel]
  have hgrowth' : m^(κ/2) ≤ A*K^3*δ^(s*(1-κ/2))/δ^(s+η) := by
    apply (mul_le_mul_iff_right₀ hm).1
    calc
      _ ≤ U*(A*K^3*δ^(s*(1-κ/2))) := hgrowth
      _ ≤ (m/δ^(s+η))*(A*K^3*δ^(s*(1-κ/2))) := by
        exact mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = _ := by ring
  have hlower : δ^(-(s+γ)*(κ/2)) ≤ m^(κ/2) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1/δ^(s+γ)) hlarge
      (show 0 ≤ κ/2 by positivity)
    rw [one_div,← Real.rpow_neg hδ.le,← Real.rpow_mul hδ.le] at hh
    exact hh
  have hpos : 0 < δ^(-(s+γ)*(κ/2)) := by positivity
  linarith only [hlower,hgrowth'.trans hcost,hpos]

end Falconer

end OAI
