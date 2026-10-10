import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance

namespace OAI

/-! # Homogeneity of the extended entropy production, including its infinite cases -/

noncomputable section

open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem extendedEntropyProduction_scale {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    extendedEntropyProduction (c*a) (c*b) = ENNReal.ofReal c*extendedEntropyProduction a b := by
  by_cases hcz : c = 0
  · subst c
    simp [extendedEntropyProduction]
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
  have hcn : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcp)
  by_cases haz : a = 0
  · subst a
    by_cases hbz : b = 0
    · subst b
      simp [extendedEntropyProduction]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
      simp [extendedEntropyProduction,hbz,(mul_pos hcp hbp).ne',hcn]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  by_cases hbz : b = 0
  · subst b
    simp [extendedEntropyProduction,haz,(mul_pos hcp hap).ne',hcn]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
  have hcap := mul_pos hcp hap
  have hcbp := mul_pos hcp hbp
  simp only [extendedEntropyProduction,hap,hbp,hcap,hcbp,haz,hbz,hcap.ne',hcbp.ne',
    and_self,↓reduceIte]
  have hdiv : c*a/(c*b) = a/b := by field_simp
  rw [hdiv,← ENNReal.ofReal_mul hc]
  congr 1
  ring

end BoltzmannNonuniqueness

end

end OAI
