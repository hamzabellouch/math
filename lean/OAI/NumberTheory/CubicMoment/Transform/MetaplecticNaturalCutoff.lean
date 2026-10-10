import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongGeometry

namespace OAI

/-! One height-independent cutoff serves both the rapid-tail estimate
and the retained mean, with all polynomial scale bounds derived. -/
noncomputable section
namespace CubicFirstMoment

def metaplecticNaturalCutoff (Y R T X δ : ℝ) : ℝ :=
  max 1 (Y^δ*(R^2*T^4/X))

lemma metaplecticNaturalCutoff_ge_one (Y R T X δ : ℝ) :
    1 ≤ metaplecticNaturalCutoff Y R T X δ := le_max_left _ _

lemma metaplecticNaturalCutoff_ratio {Y R T X δ : ℝ}
    (hY : 0 < Y) :
    (R^2*T^4/X)/metaplecticNaturalCutoff Y R T X δ ≤ Y^(-δ) := by
  have hJ : 0 < metaplecticNaturalCutoff Y R T X δ :=
    zero_lt_one.trans_le (metaplecticNaturalCutoff_ge_one _ _ _ _ _)
  apply (div_le_iff₀ hJ).mpr
  have hh := mul_le_mul_of_nonneg_left
    (show Y^δ*(R^2*T^4/X) ≤ metaplecticNaturalCutoff Y R T X δ from le_max_right _ _)
    (Real.rpow_nonneg hY.le (-δ))
  have he : Y^(-δ)*Y^δ = 1 := by rw [←Real.rpow_add hY]; simp
  simpa only [←mul_assoc,he,one_mul] using hh

lemma metaplectic_natural_length_polynomial {Y R T X B : ℝ}
    (hY : 1 ≤ Y) (hR : 0 < R) (hT : 0 < T)
    (hRB : R ≤ Y^B) (hTB : T ≤ Y^B) (hXB : Y^(-B) ≤ X) :
    R^2*T^4/X ≤ Y^(7*B) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hXp : 0 < X := (Real.rpow_pos_of_pos hYp (-B)).trans_le hXB
  have hXinv : 0 ≤ X^(-1:ℝ) := Real.rpow_nonneg hXp.le _
  have hr : R^2 ≤ Y^(2*B) := by
    apply (pow_le_pow_left₀ hR.le hRB 2).trans_eq
    rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]
    congr 1
    ring
  have ht : T^4 ≤ Y^(4*B) := by
    apply (pow_le_pow_left₀ hT.le hTB 4).trans_eq
    rw [←Real.rpow_natCast,←Real.rpow_mul hYp.le]
    congr 1
    ring
  have hx : X^(-1:ℝ) ≤ Y^B := by
    apply (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hYp _) hXB (by norm_num)).trans_eq
    rw [←Real.rpow_mul hYp.le]
    congr 1
    ring
  calc
    _ = R^2*T^4*X^(-1:ℝ) := by rw [Real.rpow_neg_one]; ring
    _ ≤ Y^(2*B)*Y^(4*B)*Y^B := by gcongr
    _ = _ := by rw [←Real.rpow_add hYp,←Real.rpow_add hYp]; congr 1; ring

lemma metaplecticNaturalCutoff_polynomial {Y R T X B δ : ℝ}
    (hY : 1 ≤ Y) (hR : 0 < R) (hT : 0 < T)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hRB : R ≤ Y^B) (hTB : T ≤ Y^B) (hXB : Y^(-B) ≤ X) :
    metaplecticNaturalCutoff Y R T X δ ≤ Y^(7*B+δ) := by
  apply max_le
  · exact Real.one_le_rpow hY (by positivity)
  · calc
      _ ≤ Y^δ*Y^(7*B) := mul_le_mul_of_nonneg_left
        (metaplectic_natural_length_polynomial hY hR hT hRB hTB hXB)
        (Real.rpow_nonneg (zero_le_one.trans hY) _)
      _ = _ := by rw [←Real.rpow_add (zero_lt_one.trans_le hY)]; congr 1; ring

end CubicFirstMoment

end

end OAI
