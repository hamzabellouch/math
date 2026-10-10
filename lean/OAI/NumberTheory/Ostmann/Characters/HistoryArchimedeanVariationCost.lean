import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationData

namespace OAI

noncomputable section
namespace Ostmann.Characters.HistoryPolynomialData
open scoped BigOperators SchwartzMap

theorem variationCost_le_exp {σ τ : Type*} [Fintype σ] [Fintype τ]
    (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ)) {A B : τ → ℝ} {M P : ℝ}
    (h : d.Ranges ρ A B M)
    (hdegree : (d.degreeCost : ℝ) ≤ Real.exp P) (hM : M ≤ Real.exp P)
    (hwidth : 3 + (∑ i : τ, (B i - A i)) ≤ Real.exp P) :
    d.variationCost A B M ≤ Real.exp (((Fintype.card τ : ℝ)+2)*P) := by
  have hw0 : 0 ≤ 3 + (∑ i : τ, (B i - A i)) :=
    add_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (h.ordered i)))
  unfold variationCost
  calc
    _ ≤ Real.exp P * ((Real.exp P)^(Fintype.card τ) * Real.exp P) := by
      exact mul_le_mul hdegree
        (mul_le_mul (pow_le_pow_left₀ h.nonneg hM _) hwidth hw0 (by positivity))
        (mul_nonneg (pow_nonneg h.nonneg _) hw0) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]
      congr 1
      ring

end Ostmann.Characters.HistoryPolynomialData

end

end OAI
