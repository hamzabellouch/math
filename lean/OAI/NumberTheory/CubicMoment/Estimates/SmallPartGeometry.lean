import OAI.NumberTheory.CubicMoment.Estimates.SmallPartCharacter

namespace OAI

/-! Conductor size and coprimality after the actual small-prime split. -/
noncomputable section
namespace CubicFirstMoment

lemma primaryOutsidePart_dvd (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    primaryOutsidePart v a ∣ a :=
  ⟨primarySmallPart v a,by rw [mul_comm,primary_small_outside_mul v ha]⟩

lemma outside_parts_coprime (v : Eisenstein) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hab : IsCoprime a b) :
    IsCoprime (primaryOutsidePart v a) (primaryOutsidePart v b) :=
  (hab.of_isCoprime_of_dvd_left (primaryOutsidePart_dvd v ha)).of_isCoprime_of_dvd_right
    (primaryOutsidePart_dvd v hb)

lemma outside_parts_coprime_local {v a b q : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v) (hq : q ∣ v) :
    IsCoprime (primaryOutsidePart v a*primaryOutsidePart v b)
      ((3*(primarySmallPart v a*primarySmallPart v b))*q) := by
  have hc := (primaryOutsidePart_coprime ha hv).mul_left (primaryOutsidePart_coprime hb hv)
  exact (hc.of_isCoprime_of_dvd_right h3).mul_right
    ((hc.of_isCoprime_of_dvd_right (primarySmallPart_dvd hsa hv)).mul_right
      (hc.of_isCoprime_of_dvd_right (primarySmallPart_dvd hsb hv))) |>.mul_right
        (hc.of_isCoprime_of_dvd_right hq)

lemma smallPartModulus_ne_zero (v : Eisenstein) {a b q : Eisenstein}
    (ha : primary a) (hb : primary b) (hq : q ≠ 0) :
    (3*(primarySmallPart v a*primarySmallPart v b))*q ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (mul_ne_zero (primary_ne_zero (primarySmallPart_primary v ha))
      (primary_ne_zero (primarySmallPart_primary v hb)))) hq

lemma smallPartModulus_norm_le {v a b q : Eisenstein}
    (hsa : Squarefree a) (hsb : Squarefree b) (hv : v ≠ 0) :
    norm ((3*(primarySmallPart v a*primarySmallPart v b))*q) ≤ 9*norm v^2*norm q := by
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  rw [norm_mul_eq,norm_mul_eq,norm_mul_eq,h3]
  have ha := norm_le_of_dvd hv (primarySmallPart_dvd hsa hv)
  have hb := norm_le_of_dvd hv (primarySmallPart_dvd hsb hv)
  have hmul := mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by norm_num : (0:ℝ) ≤ 9)) (norm_nonneg q)]

lemma primaryOutsidePart_nonunit {v a : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) (hv : v ≠ 0) (hN : norm v < norm a) :
    ¬ IsUnit (primaryOutsidePart v a) := by
  intro hu
  have h := primaryOutsidePart_norm_lower v ha hsa hv
  rw [norm_of_isUnit hu] at h
  have h' := (div_le_one (norm_pos_of_ne_zero hv)).mp h
  exact (not_le_of_gt hN) h'

end CubicFirstMoment

end

end OAI
