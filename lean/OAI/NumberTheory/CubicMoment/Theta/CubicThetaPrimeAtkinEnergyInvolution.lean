import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyValue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionInvolutive
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinatePairing

namespace OAI

/-! The prime Atkin pullback is involutive on actual sections and their
energy completion. It preserves the mass and derivative sesquilinear forms. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeAtkinMatrix_eq {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeAtkinMatrix hp=
      cubicThetaInversionMatrix (cubicThetaPrimeSquareRoot p)
        (cubicThetaPrimeSquareRoot_ne_zero hp.2.ne_zero) := by
  rw [cubicThetaPrimeAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaPrimeDilation hp.2.ne_zero : Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two]

lemma cubicThetaPrimeAtkinPoint_involutive {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaPrimeAtkinMatrix hp • (cubicThetaPrimeAtkinMatrix hp • x)=x := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeAtkinMatrix hp)
    (cubicThetaMobius (cubicThetaPrimeAtkinMatrix hp) x.val)=x.val
  rw [cubicThetaPrimeAtkinMatrix_eq,
    cubicThetaMobius_inversion _ (cubicThetaMobius_height_pos _ x.property),
    cubicThetaMobius_inversion _ x.property]
  exact cubicThetaInversion_involutive (cubicThetaPrimeSquareRoot_ne_zero hp.2.ne_zero) x.property

lemma cubicThetaPrimeAtkinSection_involutive {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) :
    cubicThetaPrimeAtkinSection hp (cubicThetaPrimeAtkinSection hp F)=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change F.val (cubicThetaPrimeAtkinMatrix hp • (cubicThetaPrimeAtkinMatrix hp • x))=F.val x
  rw [cubicThetaPrimeAtkinPoint_involutive]

theorem cubicThetaPrimeAtkinEnergy_involutive {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) :
    cubicThetaPrimeAtkinEnergy hp (cubicThetaPrimeAtkinEnergy hp u)=u := by
  refine (cubicThetaPrimeEnergyTest_dense hp).induction_on u
    (isClosed_eq ((cubicThetaPrimeAtkinEnergy hp).continuous.comp
      (cubicThetaPrimeAtkinEnergy hp).continuous) continuous_id) ?_
  intro F
  rw [cubicThetaPrimeAtkinEnergy_test,cubicThetaPrimeAtkinEnergy_test]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact cubicThetaPrimeAtkinSection_involutive hp F.val.val

lemma cubicThetaPrimeAtkinEnergy_mass_norm {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) :
    ‖cubicThetaPrimeEnergyInclusion hp (cubicThetaPrimeAtkinEnergy hp u)‖=
      ‖cubicThetaPrimeEnergyInclusion hp u‖ := by
  change ‖cubicThetaPrimeEnergyValueMap hp (cubicThetaPrimeAtkinEnergy hp u)‖=
    ‖cubicThetaPrimeEnergyValueMap hp u‖
  rw [cubicThetaPrimeAtkinEnergy_value,(cubicThetaPrimeAtkinL2 hp).norm_map]

lemma cubicThetaPrimeAtkinEnergy_mass_inner {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaPrimeEnergySpace hp) :
    inner ℂ (cubicThetaPrimeEnergyInclusion hp (cubicThetaPrimeAtkinEnergy hp u))
      (cubicThetaPrimeEnergyInclusion hp (cubicThetaPrimeAtkinEnergy hp v))=
        inner ℂ (cubicThetaPrimeEnergyInclusion hp u) (cubicThetaPrimeEnergyInclusion hp v) :=
  cubicThetaLinear_inner_of_norm_eq
    ((cubicThetaPrimeEnergyInclusion hp).toLinearMap.comp (cubicThetaPrimeAtkinEnergy hp).toLinearMap)
    (cubicThetaPrimeEnergyInclusion hp).toLinearMap (cubicThetaPrimeAtkinEnergy_mass_norm hp) u v

lemma cubicThetaPrimeAtkinEnergy_derivative_norm {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) :
    ‖cubicThetaPrimeEnergyDerivative hp (cubicThetaPrimeAtkinEnergy hp u)‖=
      ‖cubicThetaPrimeEnergyDerivative hp u‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  have h₁ := cubicThetaPrimeEnergy_norm_sq hp (cubicThetaPrimeAtkinEnergy hp u)
  have h₂ := cubicThetaPrimeEnergy_norm_sq hp u
  rw [(cubicThetaPrimeAtkinEnergy hp).norm_map,cubicThetaPrimeAtkinEnergy_mass_norm] at h₁
  linarith

lemma cubicThetaPrimeAtkinEnergy_derivative_inner {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaPrimeEnergySpace hp) :
    inner ℂ (cubicThetaPrimeEnergyDerivative hp (cubicThetaPrimeAtkinEnergy hp u))
      (cubicThetaPrimeEnergyDerivative hp (cubicThetaPrimeAtkinEnergy hp v))=
        inner ℂ (cubicThetaPrimeEnergyDerivative hp u) (cubicThetaPrimeEnergyDerivative hp v) :=
  cubicThetaLinear_inner_of_norm_eq
    ((cubicThetaPrimeEnergyDerivative hp).toLinearMap.comp (cubicThetaPrimeAtkinEnergy hp).toLinearMap)
    (cubicThetaPrimeEnergyDerivative hp).toLinearMap (cubicThetaPrimeAtkinEnergy_derivative_norm hp) u v

end CubicFirstMoment

end

end OAI
