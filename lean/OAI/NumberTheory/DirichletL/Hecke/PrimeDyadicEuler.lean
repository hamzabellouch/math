import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadic

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def eulerBound (b : ℝ) : ℝ :=
  ∑' I : NonzeroIdeal, IdealMangoldt.value I.val * (norm I)^(-b)

theorem eulerBound_summable {b : ℝ} (hb : 1<b) :
    Summable (fun I : NonzeroIdeal => IdealMangoldt.value I.val * (norm I)^(-b)) := by
  have ha (I : Ideal O) : ‖IdealEuler.normWeight 0 I‖ ≤ 1 := by
    change ‖CubicEisenstein.fullIdealWeight 0 I‖ ≤ 1
    by_cases hI : I = 0
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_left_iff.mpr (fun h => (h hI).elim), norm_zero]
      norm_num
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_right_iff.mpr (fun h => (hI h).elim)]
      simp
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (IdealEuler.normWeight 0) ha (b : ℂ) (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NonzeroIdeal => I.val))
  convert hf using 1
  ext I
  simp only [Function.comp_apply, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight,
    ite_eq_right_iff.mpr (fun h => (I.property h).elim), neg_zero, Complex.cpow_zero, one_mul]
  change IdealMangoldt.value I.val * (norm I)^(-b) =
    ‖(IdealMangoldt.value I.val : ℂ) * (norm I : ℂ)^(-(b : ℂ))‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp

theorem series_norm_le (χ : Character) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤s.re) : ‖series χ s‖ ≤ eulerBound b := by
  rw [series_eq_tsum χ (hb.trans_le hs)]
  have hbound (I : NonzeroIdeal) :
      ‖coefficient χ I.val * (norm I : ℂ)^(-s)‖ ≤
        IdealMangoldt.value I.val * (norm I)^(-b) := by
    rw [norm_mul]
    have hn : 1 ≤ norm I := by
      unfold HeckeDyadic.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hc : ‖coefficient χ I.val‖ ≤ IdealMangoldt.value I.val := by
      rw [coefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (IdealMangoldt.value_nonneg _)]
      exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg _) (idealCoeff_norm_le_one χ _)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re]
    exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))
      (Real.rpow_nonneg (norm_pos I).le _) (IdealMangoldt.value_nonneg _)

  have hf := (eulerBound_summable hb).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hbound (eulerBound_summable hb))

end SevenEighths.HeckePrimeDyadic

end

end OAI
