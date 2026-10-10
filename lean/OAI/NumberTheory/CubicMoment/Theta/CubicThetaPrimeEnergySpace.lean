import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeFiniteEnergy

namespace OAI

/-! The completed actual value-gradient graph on the finite prime
cover. The Atkin transformation extends as an isometry of this energy space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

local instance primeEnergy_addCommGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeFiniteEnergy hp) := Module.addCommMonoidToAddCommGroup ℂ

abbrev CubicThetaPrimeEnergyAmbient {p : Eisenstein} (hp : primaryPrime p) :=
  WithLp 2 (CubicThetaPrimeL2 hp × CubicThetaPrimeGradientL2 hp)

def cubicThetaPrimeEnergyGraph {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] CubicThetaPrimeEnergyAmbient hp :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (CubicThetaPrimeL2 hp) (CubicThetaPrimeGradientL2 hp)).symm.toLinearMap.comp
    ((cubicThetaPrimeEnergyValue hp).prod (cubicThetaPrimeEnergyGradient hp))

def cubicThetaPrimeEnergySpace {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (CubicThetaPrimeEnergyAmbient hp) := (cubicThetaPrimeEnergyGraph hp).range.topologicalClosure

instance cubicThetaPrimeEnergySpace_complete {p : Eisenstein} (hp : primaryPrime p) :
    CompleteSpace (cubicThetaPrimeEnergySpace hp) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaPrimeEnergyTest {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] cubicThetaPrimeEnergySpace hp :=
  (cubicThetaPrimeEnergyGraph hp).codRestrict (cubicThetaPrimeEnergySpace hp)
    (fun F => Submodule.le_topologicalClosure _ ⟨F,rfl⟩)

def cubicThetaPrimeEnergyInclusion {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeEnergySpace hp →L[ℂ] CubicThetaPrimeL2 hp :=
  (WithLp.fstL 2 ℂ (CubicThetaPrimeL2 hp) (CubicThetaPrimeGradientL2 hp)).comp
    (cubicThetaPrimeEnergySpace hp).subtypeL

def cubicThetaPrimeEnergyDerivative {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeEnergySpace hp →L[ℂ] CubicThetaPrimeGradientL2 hp :=
  (WithLp.sndL 2 ℂ (CubicThetaPrimeL2 hp) (CubicThetaPrimeGradientL2 hp)).comp
    (cubicThetaPrimeEnergySpace hp).subtypeL

lemma cubicThetaPrimeEnergyInclusion_test {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    cubicThetaPrimeEnergyInclusion hp (cubicThetaPrimeEnergyTest hp F)=cubicThetaPrimeEnergyValue hp F := rfl

lemma cubicThetaPrimeEnergyDerivative_test {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    cubicThetaPrimeEnergyDerivative hp (cubicThetaPrimeEnergyTest hp F)=cubicThetaPrimeEnergyGradient hp F := rfl

lemma cubicThetaPrimeEnergy_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) :
    ‖u‖^2=‖cubicThetaPrimeEnergyInclusion hp u‖^2+‖cubicThetaPrimeEnergyDerivative hp u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 (u:CubicThetaPrimeEnergyAmbient hp)

lemma cubicThetaPrimeEnergyTest_dense {p : Eisenstein} (hp : primaryPrime p) :
    DenseRange (cubicThetaPrimeEnergyTest hp) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (cubicThetaPrimeEnergyTest hp)=
      Set.range (cubicThetaPrimeEnergyGraph hp) := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaPrimeEnergyTest hp F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

lemma cubicThetaPrimeEnergyAtkin_test_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaPrimeEnergyTest hp (cubicThetaPrimeEnergyAtkin hp F)‖=
      ‖cubicThetaPrimeEnergyTest hp F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeEnergy_norm_sq,cubicThetaPrimeEnergy_norm_sq,
    cubicThetaPrimeEnergyInclusion_test,cubicThetaPrimeEnergyInclusion_test,
    cubicThetaPrimeEnergyDerivative_test,cubicThetaPrimeEnergyDerivative_test,
    cubicThetaPrimeEnergyValue_atkin_norm,cubicThetaPrimeEnergyGradient_atkin_norm]

def cubicThetaPrimeAtkinEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeEnergySpace hp →ₗᵢ[ℂ] cubicThetaPrimeEnergySpace hp :=
  ((cubicThetaPrimeEnergyTest hp).comp (cubicThetaPrimeEnergyAtkin hp)).extendOfIsometry
    (cubicThetaPrimeEnergyTest_dense hp) (cubicThetaPrimeEnergyAtkin_test_norm hp)

lemma cubicThetaPrimeAtkinEnergy_test {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    cubicThetaPrimeAtkinEnergy hp (cubicThetaPrimeEnergyTest hp F)=
      cubicThetaPrimeEnergyTest hp (cubicThetaPrimeEnergyAtkin hp F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
