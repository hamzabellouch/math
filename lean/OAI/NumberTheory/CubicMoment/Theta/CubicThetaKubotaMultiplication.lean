import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoprimeShear

namespace OAI

/-! The unrestricted arithmetic multiplication identity for the cubic
Kubota value at level nine. The finite shear removes the auxiliary
coprimality hypothesis from the direct reciprocity calculation. -/
noncomputable section
namespace CubicFirstMoment

lemma primary_add_nine_mul {a t c : Eisenstein} (ha : primary a)
    (ht : (9:Eisenstein) ∣ t) : primary (a+t*c) := by
  obtain ⟨u,hu⟩ := ha
  obtain ⟨v,hv⟩ := ht
  refine ⟨u+3*v*c,?_⟩
  rw [hv]
  linear_combination hu

lemma cubicThetaKubota_shear {a t c : Eisenstein} (ha : primary a)
    (ht : (9:Eisenstein) ∣ t) :
    cubicSymbol (a+t*c) c = cubicSymbol a c := by
  by_cases hc : c = 0
  · simp only [hc,mul_zero,add_zero]
  apply cubicSupplementaryPeriodicity_proved c hc _ _
    (primary_add_nine_mul ha ht) ha
  obtain ⟨u,hu⟩ := ht
  refine ⟨u,?_⟩
  rw [hu]
  ring

lemma cubicThetaKubota_product_nonzero
    {a b c d e f : Eisenstein} (ha : primary a) (he : primary e)
    (hdet : a*d-b*c = 1) (hbf : (9:Eisenstein) ∣ b*f) (hf : f ≠ 0) :
    cubicSymbol (a*e+b*f) (c*e+d*f) = cubicSymbol a c*cubicSymbol e f := by
  have hac : IsCoprime a c := ⟨d,-b,by linear_combination hdet⟩
  have ha9 : IsCoprime a 9 := by
    convert (primary_coprime_three ha).pow_right (n := 2) using 1
    norm_num
  obtain ⟨t,ht,hatf⟩ := cubicTheta_exists_coprime_shear hf (ha9.mul_right hac)
  have hbt : (9:Eisenstein) ∣ (b+t*d)*f := by
    rw [add_mul]
    exact dvd_add hbf (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ht d) f)
  have hdet' : (a+t*c)*d-(b+t*d)*c = 1 := by linear_combination hdet
  have h := cubicThetaKubota_product_coprime (primary_add_nine_mul ha ht) he
    hdet' hbt hatf
  have hA : primary (a*e+b*f) := by
    simpa only [mul_one] using primary_add_nine_mul (c := 1) (primary_mul ha he) hbf
  rw [show (a+t*c)*e+(b+t*d)*f = (a*e+b*f)+t*(c*e+d*f) by ring,
    cubicThetaKubota_shear hA ht,cubicThetaKubota_shear ha ht] at h
  exact h

/-- Arithmetic multiplication, including the zero lower-left entry. -/
theorem cubicThetaKubota_product
    {a b c d e f : Eisenstein} (ha : primary a) (he : primary e)
    (hdet : a*d-b*c = 1) (hbf : (9:Eisenstein) ∣ b*f) (hef : IsCoprime e f) :
    cubicSymbol (a*e+b*f) (c*e+d*f) = cubicSymbol a c*cubicSymbol e f := by
  by_cases hf : f = 0
  · have he1 : e = 1 := primary_unit_eq_one
      (isCoprime_zero_right.mp (hf ▸ hef)) he
    simp only [hf,he1,mul_zero,mul_one,add_zero,cubicSymbol_one_lower]
  · exact cubicThetaKubota_product_nonzero ha he hdet hbf hf

end CubicFirstMoment

end

end OAI
