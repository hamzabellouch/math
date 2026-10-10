import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFourierPairing

namespace OAI

/-! Exact two-branch action on a high-cusp Fourier source prime to p.
The identity is in the actual global automorphic L2 space. -/
noncomputable section
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialWeightScale_smooth (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    ContDiff ℝ ∞ (cubicThetaRadialWeightScale r hr W : ℝ → ℂ) :=
  hsm.comp (contDiff_const.mul contDiff_id)

lemma cubicThetaPrime_norm_one_le {p : Eisenstein} (hp : primaryPrime p) : 1≤‖(p:ℂ)‖ := by
  have hn := one_le_norm hp.2.ne_zero
  change 1≤Complex.normSq (p:ℂ) at hn
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [_root_.norm_nonneg (p:ℂ)]

lemma cubicThetaPrimeHighWeight_low {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) (v : ℝ) (hv : v≤2) : W v=0 := by
  apply hW
  exact hv.trans (by nlinarith [one_le_pow₀ (cubicThetaPrime_norm_one_le hp) (n:=3)])

lemma cubicThetaPrimeHighWeight_cube_low {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) (v : ℝ) (hv : v≤2) :
    cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
      (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) W v=0 := by
  apply hW
  change ‖(p:ℂ)‖^3*v≤2*‖(p:ℂ)‖^3
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hv (pow_nonneg (_root_.norm_nonneg (p:ℂ)) 3)

lemma cubicThetaPrimeHighWeight_one_low {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) (v : ℝ) (hv : v≤2) :
    cubicThetaRadialWeightScale ‖(p:ℂ)‖
      (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) W v=0 := by
  apply hW
  change ‖(p:ℂ)‖*v≤2*‖(p:ℂ)‖^3
  have hr := cubicThetaPrime_norm_one_le hp
  have hv' := mul_le_mul_of_nonneg_left hv (_root_.norm_nonneg (p:ℂ))
  nlinarith [sq_nonneg (‖(p:ℂ)‖-1)]

theorem cubicThetaPrimeCubeHighSource {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaPrimeCubeHeckeMass hp
      (cubicThetaHighFourierMass h W (cubicThetaPrimeHighWeight_low hp W hW) hsm)=
    cubicThetaHighFourierMass (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) W)
      (cubicThetaPrimeHighWeight_cube_low hp W hW)
      (cubicThetaRadialWeightScale_smooth _ _ W hsm)+
    star (cubicThetaPrimeCubeUnitFourier hp 1 (p*h)/(norm p:ℂ)) •
      cubicThetaHighFourierMass (p*h)
        (cubicThetaRadialWeightScale ‖(p:ℂ)‖
          (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) W)
        (cubicThetaPrimeHighWeight_one_low hp W hW)
        (cubicThetaRadialWeightScale_smooth _ _ W hsm) := by
  apply ext_inner_right ℂ
  intro v
  refine cubicThetaFiniteMassClosure_dense.induction_on v
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro F
  change inner ℂ _ (cubicThetaGlobalEnergyValueMap (cubicThetaFiniteEnergyEmbedding F))=
    inner ℂ _ (cubicThetaGlobalEnergyValueMap (cubicThetaFiniteEnergyEmbedding F))
  rw [←cubicThetaPrimeCubeHeckeMass_symmetric,cubicThetaPrimeCubeHeckeMass_energy,
    cubicThetaHighFourierMass_pairing,inner_add_left]
  rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaAutomorphicL2)]
  simp only [starRingEnd_apply,star_star]
  rw [cubicThetaHighFourierMass_pairing,cubicThetaHighFourierMass_pairing]
  exact cubicThetaPrimeCubeFourierPairing_energy hp _ h hh W hW

end CubicFirstMoment

end

end OAI
