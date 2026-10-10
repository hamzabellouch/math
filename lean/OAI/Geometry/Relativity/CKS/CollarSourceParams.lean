import OAI.Geometry.Relativity.CKS.CollarCutoffs

namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

def collarParams (R r : ℝ) : Fin 5 → ℝ :=
  ![1/r,roundingWeight R r,r*deriv (roundingWeight R) r,paddingMass R r,paddingWeight R r]

lemma collarParams_weighted : ∃ A : ℝ, 1 ≤ A ∧ ∀ R r : ℝ, 1 ≤ R → R ≤ r → r ≤ 3*R →
    (∀ i, i ≠ 0 → |collarParams R r i| ≤ A*paddingWeight R r) ∧
    ‖collarParams R r‖ ≤ A := by
  obtain ⟨B,hB,hderiv⟩ := roundingWeight_weighted_deriv
  let A := B+3
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hA2 : 2 ≤ A := by dsimp [A]; linarith
  refine ⟨A,hA1,?_⟩
  intro R r hR hr htop
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hrp : 0 < r := hRp.trans_le hr
  have hw := paddingWeight_nonneg R r
  have hw1 := paddingWeight_le_one R r
  have hparam (i : Fin 5) (hi : i ≠ 0) : |collarParams R r i| ≤ A*paddingWeight R r := by
    fin_cases i
    · exact (hi rfl).elim
    · change |roundingWeight R r| ≤ _
      rw [abs_of_nonneg (roundingWeight_nonneg _ _)]
      exact (roundingWeight_le_paddingWeight _ _).trans (by nlinarith)
    · change |r*deriv (roundingWeight R) r| ≤ _
      exact (hderiv R r hRp hr htop).trans (by dsimp [A]; nlinarith)
    · change |paddingMass R r| ≤ _
      rw [abs_of_nonneg (paddingMass_nonneg hRp hrp)]
      have hs : 1 ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt hR
      have hspos : 0 < Real.sqrt R := by positivity
      have hinv : 2/Real.sqrt R ≤ 2 := (div_le_iff₀ hspos).mpr (by nlinarith)
      exact (paddingMass_weighted_bound hRp hr).trans (by nlinarith)
    · change |paddingWeight R r| ≤ _
      rw [abs_of_nonneg hw]
      nlinarith
  refine ⟨hparam,(pi_norm_le_iff_of_nonneg (zero_le_one.trans hA1)).mpr ?_⟩
  intro i
  rw [Real.norm_eq_abs]
  by_cases hi : i=0
  · subst i
    change |1/r| ≤ A
    rw [abs_of_pos (by positivity : 0 < 1/r)]
    exact (one_div_le_one_div_of_le zero_lt_one (hR.trans hr)).trans (by simpa using hA1)
  · exact (hparam i hi).trans (by nlinarith)

end
end CKSBending

end

end OAI
