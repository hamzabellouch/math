import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSelfAdjoint
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyValue

namespace OAI

/-! The same cubed-prime correspondence on the actual automorphic mass
space. It agrees with the energy operator and is self-adjoint there. -/
noncomputable section
namespace CubicFirstMoment

local instance cubeMass_finiteGroup : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaFiniteMassClosure : cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaAutomorphicL2 :=
  cubicThetaGlobalEnergyValueMap.toLinearMap.comp cubicThetaFiniteEnergyEmbedding

lemma cubicThetaFiniteMassClosure_val (F : cubicThetaFiniteEnergySections) :
    (cubicThetaFiniteMassClosure F).val=cubicThetaFiniteEnergyValue F := rfl

lemma cubicThetaFiniteMassClosure_dense : DenseRange cubicThetaFiniteMassClosure := by
  have he : (fun F : cubicThetaSmoothTests =>
      cubicThetaFiniteMassClosure (cubicThetaSmoothToFiniteEnergy F))=
      (fun F => cubicThetaGlobalMassClosure F) := rfl
  have hd : DenseRange (fun F : cubicThetaSmoothTests =>
      cubicThetaFiniteMassClosure (cubicThetaSmoothToFiniteEnergy F)) := by
    rw [he]
    exact cubicThetaGlobalMassClosure_dense
  exact hd.of_comp

def cubicThetaPrimeCubeRawMass {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaAutomorphicL2 :=
  cubicThetaFiniteMassClosure.comp (cubicThetaPrimeCubeHeckeFiniteLinear hp)

lemma cubicThetaPrimeCubeRawMass_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaPrimeCubeRawMass hp F‖≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
      ‖cubicThetaFiniteMassClosure F‖ := by
  change ‖cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp F)‖≤
    ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*‖cubicThetaFiniteEnergyValue F‖
  apply _root_.le_of_sq_le_sq _ (mul_nonneg (Nat.cast_nonneg _) (_root_.norm_nonneg _))
  simpa only [mul_pow] using cubicThetaPrimeCubeHeckeFinite_value_bound hp F

def cubicThetaPrimeCubeHeckeMass {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →L[ℂ] cubicThetaAutomorphicL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (cubicThetaPrimeCubeRawMass hp) cubicThetaFiniteMassClosure

lemma cubicThetaPrimeCubeHeckeMass_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPrimeCubeHeckeMass hp (cubicThetaFiniteMassClosure F)=
      cubicThetaFiniteMassClosure (cubicThetaPrimeCubeHeckeFinite hp F) :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaPrimeCubeRawMass hp) (e:=cubicThetaFiniteMassClosure)
    cubicThetaFiniteMassClosure_dense
    ⟨((cubicThetaPrimeIwahori (p^3)).index:ℝ),cubicThetaPrimeCubeRawMass_bound hp⟩ F

theorem cubicThetaPrimeCubeHeckeMass_energy {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeCubeHeckeMass hp (cubicThetaGlobalEnergyValueMap u)=
      cubicThetaGlobalEnergyValueMap (cubicThetaPrimeCubeHeckeEnergy hp u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeHeckeMass hp).continuous.comp
      cubicThetaGlobalEnergyValueMap.continuous)
      (cubicThetaGlobalEnergyValueMap.continuous.comp (cubicThetaPrimeCubeHeckeEnergy hp).continuous)) ?_
  intro F
  change cubicThetaPrimeCubeHeckeMass hp (cubicThetaFiniteMassClosure F)=_
  rw [cubicThetaPrimeCubeHeckeMass_finite,cubicThetaPrimeCubeHeckeEnergy_finite]
  rfl

theorem cubicThetaPrimeCubeHeckeMass_bound {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) :
    ‖cubicThetaPrimeCubeHeckeMass hp u‖≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)*‖u‖ := by
  refine cubicThetaFiniteMassClosure_dense.induction_on u
    (isClosed_le (cubicThetaPrimeCubeHeckeMass hp).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro F
  rw [cubicThetaPrimeCubeHeckeMass_finite]
  exact cubicThetaPrimeCubeRawMass_bound hp F

theorem cubicThetaPrimeCubeHeckeMass_symmetric {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ u (cubicThetaPrimeCubeHeckeMass hp v)=
      inner ℂ (cubicThetaPrimeCubeHeckeMass hp u) v := by
  apply cubicThetaFiniteMassClosure_dense.induction_on₂
    (p:=fun u v => inner ℂ u (cubicThetaPrimeCubeHeckeMass hp v)=
      inner ℂ (cubicThetaPrimeCubeHeckeMass hp u) v) ?_ ?_ u v
  · apply isClosed_eq
    · exact continuous_fst.inner ((cubicThetaPrimeCubeHeckeMass hp).continuous.comp continuous_snd)
    · exact ((cubicThetaPrimeCubeHeckeMass hp).continuous.comp continuous_fst).inner continuous_snd
  · intro F G
    rw [cubicThetaPrimeCubeHeckeMass_finite,cubicThetaPrimeCubeHeckeMass_finite]
    have he := cubicThetaPrimeCubeHecke_mass_symmetric hp
      (cubicThetaFiniteEnergyEmbedding F) (cubicThetaFiniteEnergyEmbedding G)
    rw [cubicThetaPrimeCubeHeckeEnergy_finite,cubicThetaPrimeCubeHeckeEnergy_finite] at he
    exact he

end CubicFirstMoment

end

end OAI
