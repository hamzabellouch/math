import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointC1Section

namespace OAI

/-! Global inversion on actual finite-energy C1 sections. This bridges
the completed inversion to the literal functions occurring in the Hecke trace. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInversionSection_c1 (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaInversionSection F)) {y : ℂ × ℝ | 0<y.2} := by
  exact (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion)
    (cubicThetaSectionPointC1 F hF)).property

lemma cubicThetaInversionPointC1 (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaSectionPointC1 (cubicThetaInversionSection F) (cubicThetaInversionSection_c1 F hF)=
      cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion)
        (cubicThetaSectionPointC1 F hF) := rfl

lemma cubicThetaInversionSection_C1energy (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (x : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaInversionSection F) x=
      cubicThetaSectionEnergy F (cubicThetaFullInversion • x) := by
  rw [←cubicThetaSectionGradient_norm_sq,←cubicThetaSectionGradient_norm_sq,
    ←cubicThetaSectionPointC1_gradient _ (cubicThetaInversionSection_c1 F hF),
    ←cubicThetaSectionPointC1_gradient _ hF,cubicThetaInversionPointC1,
    cubicThetaPointC1Pullback_gradient_norm]
  rfl

def cubicThetaInversionFinite (F : cubicThetaFiniteEnergySections) : cubicThetaFiniteEnergySections :=
  ⟨cubicThetaInversionSection F.val,cubicThetaInversionSection_c1 F.val F.property.1,
    cubicThetaInversionSection_memLp F.val F.property.2.1,
    cubicThetaPrimeCubeGradient_memLp_of_domain _ (cubicThetaInversionSection_c1 F.val F.property.1) (by
      have hi := cubicThetaScalarInversion_integrable (cubicThetaPrimeCubeFinite_energy_domain F)
        (cubicThetaC1Energy_invariant F.val F.property.1)
      change IntegrableOn (fun x => cubicThetaSectionEnergy (cubicThetaInversionSection F.val) x)
        cubicThetaFundamentalDomain cubicThetaPointMeasure
      simpa only [cubicThetaInversionSection_C1energy F.val F.property.1] using hi)⟩

def cubicThetaInversionFiniteLinear : cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaFiniteEnergySections where
  toFun := cubicThetaInversionFinite
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma cubicThetaInversionFinite_value_norm (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyValue (cubicThetaInversionFinite F)‖^2=
      ‖cubicThetaFiniteEnergyValue F‖^2 := by
  rw [cubicThetaFiniteEnergyValue_domain_norm_sq,cubicThetaFiniteEnergyValue_domain_norm_sq]
  exact cubicThetaInversion_domain_integral F.val

lemma cubicThetaInversionFinite_gradient_norm (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyGradient (cubicThetaInversionFinite F)‖^2=
      ‖cubicThetaFiniteEnergyGradient F‖^2 := by
  rw [cubicThetaFiniteEnergyGradient_domain_norm_sq,cubicThetaFiniteEnergyGradient_domain_norm_sq]
  change (∫ x in cubicThetaFundamentalDomain,
    cubicThetaSectionEnergy (cubicThetaInversionSection F.val) x ∂cubicThetaPointMeasure)=_
  simp_rw [cubicThetaInversionSection_C1energy F.val F.property.1]
  exact cubicThetaScalarInversion_integral (cubicThetaC1Energy_invariant F.val F.property.1)

lemma cubicThetaInversionFinite_embedding_norm (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyEmbedding (cubicThetaInversionFinite F)‖=
      ‖cubicThetaFiniteEnergyEmbedding F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaGlobalEnergy_norm_sq]
  exact congrArg₂ (·+·) (cubicThetaInversionFinite_value_norm F)
    (cubicThetaInversionFinite_gradient_norm F)

end CubicFirstMoment

end

end OAI
