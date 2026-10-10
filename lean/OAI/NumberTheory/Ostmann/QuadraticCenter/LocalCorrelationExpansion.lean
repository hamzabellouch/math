import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationDefs

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem correlation_phase_average {q : ℕ} [NeZero q] (a b h : ZMod q) :
    (∑ s : ZMod q, ZMod.stdAddChar (-(a * s)) *
      ZMod.stdAddChar (b * s) * ZMod.stdAddChar (-(s * h))) / (q : ℂ) =
        if a - b = -h then 1 else 0 := by
  have hp (s : ZMod q) :
      ZMod.stdAddChar (-(a * s)) * ZMod.stdAddChar (b * s) *
          ZMod.stdAddChar (-(s * h)) = ZMod.stdAddChar (s * (-a + b - h)) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hp]
  rw [normalized_phase_sum]
  have heq : (-a + b - h = 0) ↔ (a - b = -h) := by
    constructor <;> intro hh <;> linear_combination -hh
  simp only [heq]

theorem correlation_coefficient_expansion {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (hdq : d ∣ q) (heq : e ∣ q) (f : ZMod d → ℂ) (g : ZMod e → ℂ) (h : ZMod q) :
    normalizedCoefficient (transformCorrelation hdq heq f g) h =
      (∑ x : ZMod d, ∑ y : ZMod e,
        if frequencyEmbedding (q := q) x - frequencyEmbedding (q := q) y = -h
          then f x * conj (g y) else 0) / ((Real.sqrt d : ℂ) * (Real.sqrt e : ℂ)) := by
  classical
  calc
    _ = (∑ x : ZMod d, ∑ y : ZMod e, f x * conj (g y) *
        ((∑ s : ZMod q, ZMod.stdAddChar (-(frequencyEmbedding (q := q) x * s)) *
          ZMod.stdAddChar (frequencyEmbedding (q := q) y * s) *
          ZMod.stdAddChar (-(s * h))) / (q : ℂ))) /
        ((Real.sqrt d : ℂ) * (Real.sqrt e : ℂ)) := by
      unfold normalizedCoefficient
      rw [ZMod.dft_apply]
      simp only [transformCorrelation, unitaryDFT_restrict_expansion, smul_eq_mul,
        map_sum, map_mul, Complex.conj_ofReal, Supply.conj_stdAddChar, neg_neg,
        div_eq_mul_inv, mul_inv_rev, map_inv₀, Complex.conj_ofReal]
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_lhs =>
        arg 2
        intro s
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by
      simp_rw [correlation_phase_average]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp

end Ostmann.QuadraticCenter

end

end OAI
