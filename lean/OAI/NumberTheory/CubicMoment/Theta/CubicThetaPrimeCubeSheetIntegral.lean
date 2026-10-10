import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeAtkinIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeDegree

namespace OAI

/-! Exact integrals on the finite cubed-prime covering. Original invariant
functions gain exactly the computed index, with integrability preserved. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeSheetIntegral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure)=
      ∑' t : cubicThetaPrimeCubeTransversal p,
        ∫ x in cubicThetaFundamentalDomain,f (t.val • x) ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hmeas (t : cubicThetaPrimeCubeTransversal p) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image' cubicThetaFundamentalDomain_measurable
  have hint (t : cubicThetaPrimeCubeTransversal p) :
      IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        cubicThetaPointMeasure :=
    hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  change (∫ x in ⋃ t : cubicThetaPrimeCubeTransversal p,
    (fun y : CubicThetaPoint => t.val • y) '' cubicThetaFundamentalDomain,f x
      ∂cubicThetaPointMeasure)=_
  rw [integral_iUnion_fintype hmeas (cubicThetaPrimeCubeCoverDomain_disjoint p) hint]
  apply Finset.sum_congr rfl
  intro t _
  exact (measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul t.val) f cubicThetaFundamentalDomain

lemma cubicThetaPrimeCubeInvariant_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ} (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro t
    exact ((cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).integrableOn_iff
      (cubicThetaIntegralImage_fundamental t.val.val) hi).mp hf
  · exact Summable.of_finite

theorem cubicThetaPrimeCubeInvariant_integral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ} (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure)=
      ((normNat p)^3+(normNat p)^2:ℝ)*
        ∫ x in cubicThetaFundamentalDomain,f x ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  rw [cubicThetaPrimeCubeSheetIntegral hp (cubicThetaPrimeCubeInvariant_integrable hp hf hi)]
  simp_rw [hi]
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,
    (cubicThetaPrimeCubeTransversal_complement p).card_right,cubicThetaPrimeCubeIwahori_index hp]
  simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_pow]

end CubicFirstMoment

end

end OAI
