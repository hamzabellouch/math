import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeLinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRestriction

namespace OAI

/-! The actual cubed-prime Hecke correspondence on the completed global
energy space. The extension is determined by its literal action
on the dense finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

local instance cubicThetaCubeFinite_addGroup : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeCubeHeckeRawEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaFiniteEnergyEmbedding.comp (cubicThetaPrimeCubeHeckeFiniteLinear hp)

lemma cubicThetaPrimeCubeHeckeRawEnergy_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaPrimeCubeHeckeRawEnergy hp F‖^2≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyEmbedding F‖^2 := by
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaGlobalEnergy_norm_sq]
  change ‖cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp F)‖^2+
      ‖cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeHeckeFinite hp F)‖^2≤
    ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*
      (‖cubicThetaFiniteEnergyValue F‖^2+‖cubicThetaFiniteEnergyGradient F‖^2)
  calc
    _ ≤ ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyValue F‖^2+
        ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyGradient F‖^2 :=
      add_le_add (cubicThetaPrimeCubeHeckeFinite_value_bound hp F)
        (cubicThetaPrimeCubeHeckeFinite_gradient_bound hp F)
    _ = _ := by ring

lemma cubicThetaPrimeCubeHeckeRawEnergy_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaPrimeCubeHeckeRawEnergy hp F‖≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  apply _root_.le_of_sq_le_sq _ (mul_nonneg (Nat.cast_nonneg _) (_root_.norm_nonneg _))
  simpa only [mul_pow] using cubicThetaPrimeCubeHeckeRawEnergy_norm_sq hp F

def cubicThetaPrimeCubeHeckeEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (cubicThetaPrimeCubeHeckeRawEnergy hp) cubicThetaFiniteEnergyEmbedding

lemma cubicThetaPrimeCubeHeckeEnergy_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPrimeCubeHeckeEnergy hp (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaPrimeCubeHeckeRawEnergy hp F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaPrimeCubeHeckeRawEnergy hp) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense
    ⟨((cubicThetaPrimeIwahori (p^3)).index:ℝ),cubicThetaPrimeCubeHeckeRawEnergy_bound hp⟩ F

theorem cubicThetaPrimeCubeHeckeEnergy_bound {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaPrimeCubeHeckeEnergy hp u‖≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)*‖u‖ := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_le (cubicThetaPrimeCubeHeckeEnergy hp).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro F
  rw [cubicThetaPrimeCubeHeckeEnergy_finite]
  exact cubicThetaPrimeCubeHeckeRawEnergy_bound hp F

end CubicFirstMoment

end

end OAI
