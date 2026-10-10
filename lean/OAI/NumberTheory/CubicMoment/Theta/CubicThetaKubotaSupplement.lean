import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaValue
import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof

namespace OAI

/-! The elementary supplementary-law calculation used for the Kubota
multiplier in DR v3 Remark 5.1. -/
noncomputable section
namespace CubicFirstMoment

/-- The unit and ramified factors need only congruence modulo nine;
the primary factor needs congruence modulo the numerator itself. -/
lemma cubicSymbol_periodic_of_nine_and_numerator {a b c : Eisenstein}
    (ha : primary a) (hb : primary b) (h9 : (9:Eisenstein) ∣ a-b)
    (hc : c ∣ a-b) : cubicSymbol a c = cubicSymbol b c := by
  by_cases hc0 : c = 0
  · rw [hc0,zero_dvd_iff] at hc
    rw [sub_eq_zero.mp hc]
  · obtain ⟨u,k,d,hd,he⟩ := unit_ramified_primary_decomposition hc0
    have hdc : d ∣ c := by
      refine ⟨(u:Eisenstein)*lambdaE^k,?_⟩
      rw [he]
      ring
    have hds : cubicSymbol a d = cubicSymbol b d := by
      rw [cubic_reciprocity ha hd,cubic_reciprocity hb hd]
      exact cubicSymbol_congr (residue_eq_of_dvd_sub (dvd_trans hdc hc))
    rw [he,cubicSymbol_mul_upper ha,cubicSymbol_mul_upper ha,
      cubicSymbol_mul_upper hb,cubicSymbol_mul_upper hb,
      cubicSymbol_pow_upper ha,cubicSymbol_pow_upper hb,
      cubicSymbol_unit_periodic ha hb u.isUnit h9,
      cubicSymbol_lambda_periodic ha hb h9,hds]

/-- If a primary denominator is one modulo nine and modulo the numerator,
all unit, ramified and primary parts of its cubic residue value are one. -/
lemma cubicThetaKubota_symbol_one {D c : Eisenstein} (hD : primary D)
    (h9 : (9:Eisenstein) ∣ D-1) (hc : c ∣ D-1) : cubicSymbol D c = 1 := by
  by_cases hc0 : c = 0
  · rw [hc0,zero_dvd_iff] at hc
    have hD1 : D = 1 := sub_eq_zero.mp hc
    rw [hD1,cubicSymbol_one_lower]
  · obtain ⟨u,k,a,ha,he⟩ := unit_ramified_primary_decomposition hc0
    have hu : cubicSymbol D (u:Eisenstein) = 1 := by
      rw [cubicSymbol_unit_periodic hD primary_one u.isUnit h9,cubicSymbol_one_lower]
    have hl : cubicSymbol D lambdaE = 1 := by
      rw [cubicSymbol_lambda_periodic hD primary_one h9,cubicSymbol_one_lower]
    have hca : a ∣ c := by
      refine ⟨(u:Eisenstein)*lambdaE^k,?_⟩
      rw [he]
      ring
    have haD := dvd_trans hca hc
    have hs : cubicSymbol D a = 1 := by
      rw [cubic_reciprocity hD ha,cubicSymbol_congr (residue_eq_of_dvd_sub haD),
        cubic_reciprocity ha primary_one,cubicSymbol_one_lower]
    rw [he,cubicSymbol_mul_upper hD,cubicSymbol_mul_upper hD,cubicSymbol_pow_upper hD,
      hu,hl,hs,one_pow,mul_one,mul_one]

end CubicFirstMoment

end

end OAI
