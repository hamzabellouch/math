import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLiftEnergy

namespace OAI

/-! Compatibility of the completed prime energy graph with the actual
automorphic L2 space, its Atkin action, and the normalized original lift. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeEnergyFiniteSection {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] cubicThetaPrimeFiniteSections hp where
  toFun F := ⟨F.val.val,F.property.1⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeEnergyInclusion_mem {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) :
    cubicThetaPrimeEnergyInclusion hp u∈cubicThetaPrimeAutomorphicL2 hp := by
  let P := WithLp.fstL 2 ℂ (CubicThetaPrimeL2 hp) (CubicThetaPrimeGradientL2 hp)
  have hr : (cubicThetaPrimeEnergyGraph hp).range ≤
      (cubicThetaPrimeAutomorphicL2 hp).comap P.toLinearMap := by
    rintro x ⟨F,rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨cubicThetaPrimeEnergyFiniteSection hp F,rfl⟩
  have hc : IsClosed ((cubicThetaPrimeAutomorphicL2 hp).comap P.toLinearMap :
      Set (CubicThetaPrimeEnergyAmbient hp)) :=
    (Submodule.isClosed_topologicalClosure _).preimage P.continuous
  exact (cubicThetaPrimeEnergyGraph hp).range.topologicalClosure_minimal hr hc u.property

def cubicThetaPrimeEnergyValueMap {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeEnergySpace hp →L[ℂ] cubicThetaPrimeAutomorphicL2 hp :=
  (cubicThetaPrimeEnergyInclusion hp).codRestrict _ (cubicThetaPrimeEnergyInclusion_mem hp)

lemma cubicThetaPrimeEnergyValueMap_test {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    cubicThetaPrimeEnergyValueMap hp (cubicThetaPrimeEnergyTest hp F)=
      cubicThetaPrimeFiniteEmbedding hp (cubicThetaPrimeEnergyFiniteSection hp F) := rfl

def cubicThetaGlobalEnergyValueMap : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaAutomorphicL2 :=
  cubicThetaGlobalInclusion.codRestrict _ cubicThetaGlobalInclusion_mem

lemma cubicThetaGlobalEnergyValueMap_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalEnergyValueMap (cubicThetaGlobalEnergyTest F)=cubicThetaGlobalMassClosure F := rfl

theorem cubicThetaPrimeLiftEnergy_value {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeEnergyValueMap hp (cubicThetaPrimeLiftEnergy hp u)=
      cubicThetaPrimeLiftL2 hp (cubicThetaGlobalEnergyValueMap u) := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeEnergyValueMap hp).continuous.comp
      (cubicThetaPrimeLiftEnergy hp).continuous)
      ((cubicThetaPrimeLiftL2 hp).continuous.comp cubicThetaGlobalEnergyValueMap.continuous)) ?_
  intro F
  change cubicThetaPrimeEnergyValueMap hp (cubicThetaPrimeLiftEnergy hp
    (cubicThetaGlobalEnergyTest F))=
      cubicThetaPrimeLiftL2 hp (cubicThetaGlobalEnergyValueMap (cubicThetaGlobalEnergyTest F))
  rw [cubicThetaPrimeLiftEnergy_smooth,cubicThetaGlobalEnergyValueMap_test,
    cubicThetaPrimeLiftL2_smooth]
  change cubicThetaPrimeEnergyValueMap hp
    (((Real.sqrt ((cubicThetaPrimeCoverGroup hp).index:ℝ))⁻¹:ℂ) •
      cubicThetaPrimeEnergyTest hp (cubicThetaPrimeSmoothEnergyRestriction hp F))=_
  rw [map_smul,cubicThetaPrimeEnergyValueMap_test]
  rfl

theorem cubicThetaPrimeAtkinEnergy_value {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) :
    cubicThetaPrimeEnergyValueMap hp (cubicThetaPrimeAtkinEnergy hp u)=
      cubicThetaPrimeAtkinL2 hp (cubicThetaPrimeEnergyValueMap hp u) := by
  refine (cubicThetaPrimeEnergyTest_dense hp).induction_on u
    (isClosed_eq ((cubicThetaPrimeEnergyValueMap hp).continuous.comp
      (cubicThetaPrimeAtkinEnergy hp).continuous)
      ((cubicThetaPrimeAtkinL2 hp).continuous.comp (cubicThetaPrimeEnergyValueMap hp).continuous)) ?_
  intro F
  rw [cubicThetaPrimeAtkinEnergy_test,cubicThetaPrimeEnergyValueMap_test,
    cubicThetaPrimeEnergyValueMap_test,cubicThetaPrimeAtkinL2_finite]
  rfl

end CubicFirstMoment

end

end OAI
