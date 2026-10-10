import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantCharacter

namespace OAI

/-! Splitting an unramified primary factor from the actual Eisenstein
row weight. Common-factor zeros are retained in every identity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_factor {u : Eisenstein} (hu : primary u)
    (c d : Eisenstein) :
    cubicThetaEisensteinWeight (u*c) d=
      cubicSymbol u d*cubicThetaEisensteinWeight c d := by
  by_cases hd : primary d
  · by_cases hcu : IsCoprime u d
    · unfold cubicThetaEisensteinWeight
      rw [IsCoprime.mul_left_iff,and_iff_right hcu]
      split_ifs with hcd
      · rw [cubicSymbol_mul_upper hd,cubic_reciprocity hd hu]
      · simp
    · have hz := cubicSymbol_eq_zero_of_not_isCoprime hu hcu
      have huc : ¬IsCoprime (u*c) d := fun h => hcu h.of_mul_left_left
      simp only [cubicThetaEisensteinWeight,huc,and_false,ite_false,hz,zero_mul]
  · simp [cubicThetaEisensteinWeight,hd]

lemma cubicThetaEisensteinWeight_mix {u c : Eisenstein} (hu : primary u)
    (hc : (3:Eisenstein) ∣ c) (hcu : IsCoprime c u) (x y : Eisenstein) :
    cubicThetaEisensteinWeight (u*c) (3*c*x+u*y)=
      (cubicSymbol u (3*c)*cubicSymbol u c)*cubicSymbol u x*
        cubicThetaEisensteinWeight c y := by
  rw [cubicThetaEisensteinWeight_factor hu]
  have hs : cubicSymbol u (3*c*x+u*y)=cubicSymbol u (3*c*x) := by
    apply cubicSymbol_congr
    have hz : Ideal.Quotient.mk (modulus u) u=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl u))
    simp only [map_add,map_mul,hz,zero_mul,add_zero]
  have hw : cubicThetaEisensteinWeight c (3*c*x+u*y)=cubicThetaEisensteinWeight c (u*y) := by
    rw [add_comm (3*c*x)]
    exact cubicThetaEisensteinWeight_periodic hc (u*y) x
  rw [hs,hw,cubicSymbol_mul_upper hu,cubicThetaEisensteinWeight_mul hu hcu]
  ring

lemma cubicThetaEisensteinWeight_congr {c d e : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (he : Ideal.Quotient.mk (modulus (3*c)) d=Ideal.Quotient.mk (modulus (3*c)) e) :
    cubicThetaEisensteinWeight c d=cubicThetaEisensteinWeight c e := by
  rw [← cubicThetaEisensteinResidueWeight_mk hc,← cubicThetaEisensteinResidueWeight_mk hc,he]

lemma cubicThetaEisensteinWeight_congr_of_eq {q c d e : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hq : q=3*c)
    (he : Ideal.Quotient.mk (modulus q) d=Ideal.Quotient.mk (modulus q) e) :
    cubicThetaEisensteinWeight c d=cubicThetaEisensteinWeight c e := by
  subst q
  exact cubicThetaEisensteinWeight_congr hc he

end CubicFirstMoment

end

end OAI
