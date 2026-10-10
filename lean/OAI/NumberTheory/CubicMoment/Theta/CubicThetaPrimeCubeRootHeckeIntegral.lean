import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootHeckeCover
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSheetIntegral

namespace OAI

/-! Exact finite-index integral transport to the actual cubic root domain.
The statement is used for real masses and complex pairings alike. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootHecke_disjoint {p : Eisenstein} (hp : primaryPrime p) :
    Pairwise (fun t u : cubicThetaPrimeCubeRootHeckeTransversal hp =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaPrimeCubeCoverDomain p)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaPrimeCubeCoverDomain p)) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hga⟩ ⟨b,hb,hgb⟩
  dsimp only at hga hgb
  have hm : (u.val⁻¹*t.val) • a=b := by rw [mul_smul,hga,←hgb,inv_smul_smul]
  have he : u.val⁻¹*t.val=1 := (cubicThetaPrimeCubeCoverDomain_unique p a).unique
    (by rwa [hm]) (by simpa using ha)
  exact htu (Subtype.ext (inv_mul_eq_one.mp he).symm)

section Integral
variable {E : Type*} [NormedAddCommGroup E]

lemma cubicThetaPrimeCubeRootHecke_relative_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → E}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    IntegrableOn f (cubicThetaPrimeCubeRootHeckeDomain hp) cubicThetaPointMeasure := by
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro t
    apply ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
      (measurableEmbedding_const_smul t.val)).mpr
    simpa only [Function.comp_def,hi] using hf
  · exact Summable.of_finite

lemma cubicThetaPrimeCubeRootHecke_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → E}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    IntegrableOn f (cubicThetaPrimeCubeRootCoverDomain hp) cubicThetaPointMeasure := by
  have hk (g : cubicThetaPrimeCubeRootCoverGroup hp) (x : CubicThetaPoint) : f (g • x)=f x :=
    hi ⟨g.val,cubicThetaPrimeCubeRoot_le_hecke hp g.property⟩ x
  exact ((cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaPrimeCubeRootHeckeDomain_root_fundamental hp cubicThetaPointMeasure) hk).mpr
    (cubicThetaPrimeCubeRootHecke_relative_integrable hp hf hi)

theorem cubicThetaPrimeCubeRootHecke_integral {p : Eisenstein} (hp : primaryPrime p)
    [NormedSpace ℝ E]
    {f : CubicThetaPoint → E}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,f x ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℝ) •
        ∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure := by
  let : Fintype (cubicThetaPrimeCubeRootHeckeTransversal hp) := Fintype.ofFinite _
  have hk (g : cubicThetaPrimeCubeRootCoverGroup hp) (x : CubicThetaPoint) : f (g • x)=f x :=
    hi ⟨g.val,cubicThetaPrimeCubeRoot_le_hecke hp g.property⟩ x
  rw [(cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeCubeRootHeckeDomain_root_fundamental hp cubicThetaPointMeasure) hk]
  have hmeas (t : cubicThetaPrimeCubeRootHeckeTransversal hp) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaPrimeCubeCoverDomain p) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image'
      (cubicThetaPrimeCubeCoverDomain_measurable hp)
  have hint (t : cubicThetaPrimeCubeRootHeckeTransversal hp) :
      IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaPrimeCubeCoverDomain p)
        cubicThetaPointMeasure := by
    apply ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
      (measurableEmbedding_const_smul t.val)).mpr
    simpa only [Function.comp_def,hi] using hf
  change (∫ x in ⋃ t : cubicThetaPrimeCubeRootHeckeTransversal hp,
    (fun y : CubicThetaPoint => t.val • y) '' cubicThetaPrimeCubeCoverDomain p,f x
      ∂cubicThetaPointMeasure)=_
  rw [integral_iUnion_fintype hmeas (cubicThetaPrimeCubeRootHecke_disjoint hp) hint]
  have ht (t : cubicThetaPrimeCubeRootHeckeTransversal hp) :
      (∫ x in (fun y : CubicThetaPoint => t.val • y) '' cubicThetaPrimeCubeCoverDomain p,
        f x ∂cubicThetaPointMeasure)=∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure := by
    rw [(measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
      (measurableEmbedding_const_smul t.val) f (cubicThetaPrimeCubeCoverDomain p)]
    simp only [hi]
  simp only [ht,Finset.sum_const,Finset.card_univ]
  rw [←Nat.card_eq_fintype_card,(cubicThetaPrimeCubeRootHeckeTransversal_complement hp).card_right,
    Nat.cast_smul_eq_nsmul ℝ]

end Integral
end CubicFirstMoment

end

end OAI
