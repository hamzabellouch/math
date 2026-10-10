import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaAlternative

namespace OAI

/-! The coprime-column step of the Kubota multiplication law at level nine.
It is proved from cubic reciprocity and the already discharged supplementary
periodicity, not imposed as a new character input. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaKubota_product_coprime
    {a b c d e f : Eisenstein} (ha : primary a) (he : primary e)
    (hdet : a*d-b*c = 1) (hbf : (9:Eisenstein) ∣ b*f)
    (haf : IsCoprime a f) :
    cubicSymbol (a*e+b*f) (c*e+d*f) = cubicSymbol a c*cubicSymbol e f := by
  let A := a*e+b*f
  let C := c*e+d*f
  have hA : primary A := by
    have hb3 : (3:Eisenstein) ∣ b*f := dvd_trans
      (show (3:Eisenstein) ∣ 9 from ⟨3,by norm_num⟩) hbf
    have ht := dvd_add (primary_mul ha he) hb3
    change (3:Eisenstein) ∣ A-1
    rw [show A-1 = a*e-1+b*f by dsimp [A]; ring]
    exact ht
  have hA9 : (9:Eisenstein) ∣ A-a*e := by simpa only [A,add_sub_cancel_left] using hbf
  have hAf : f ∣ A-a*e := by
    simpa only [A,add_sub_cancel_left] using dvd_mul_left f b
  have hsymbol : cubicSymbol A f = cubicSymbol a f*cubicSymbol e f := by
    rw [cubicSymbol_periodic_of_nine_and_numerator hA (primary_mul ha he) hA9 hAf,
      cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero he)]
  have hac : A ∣ a*C-f := by
    refine ⟨c,?_⟩
    dsimp [A,C]
    linear_combination f*hdet
  have haa : a ∣ A-b*f := by
    refine ⟨e,?_⟩
    dsimp [A]
    ring
  have hm : (cubicSymbol a b*cubicSymbol a f)*cubicSymbol A C =
      cubicSymbol a f*cubicSymbol e f := by
    calc
      _ = cubicSymbol A (a*C) := by
        rw [cubicSymbol_mul_upper hA,cubic_reciprocity hA ha,
          cubicSymbol_congr (residue_eq_of_dvd_sub haa),cubicSymbol_mul_upper ha]
      _ = cubicSymbol A f := cubicSymbol_congr (residue_eq_of_dvd_sub hac)
      _ = _ := hsymbol
  have hacb : a ∣ c*b-(-1) := by
    refine ⟨d,?_⟩
    linear_combination -hdet
  have hcb : cubicSymbol a c*cubicSymbol a b = 1 := by
    rw [←cubicSymbol_mul_upper ha,cubicSymbol_congr (residue_eq_of_dvd_sub hacb),
      cubicSymbol_neg ha,cubic_reciprocity ha primary_one,cubicSymbol_one_lower]
  have hX : cubicSymbol a f ≠ 0 := by
    intro hz
    have h := norm_cubicSymbol_of_isCoprime ha haf
    rw [hz,norm_zero] at h
    norm_num at h
  change cubicSymbol A C = _
  apply mul_left_cancel₀ hX
  linear_combination (cubicSymbol a c)*hm -
    (cubicSymbol a f*cubicSymbol A C)*hcb

end CubicFirstMoment

end

end OAI
