import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CoherentPackets
import OAI.Analysis.CoulombIonization.Variational.SmearingPotential

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RadialPacket_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma radial_potential_le_point {η : Space → ℝ} (hη : Integrable η)
    (hp : MemLp η (5/3 : ENNReal)) (hn : ∀ x, 0 ≤ η x)
    (hr : CoulombAnalysis.IsRadial η) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, η y ≠ 0 → ‖y‖ ≤ R) {x : Space} (hx : x ≠ 0) :
    CoulombAnalysis.tfPotential η x ≤ (∫ y, η y)/‖x‖ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let S : Set Space := {y | ‖y‖ ≤ ‖x‖}
  have hm : MeasurableSet S := measurableSet_le measurable_norm measurable_const
  have he : Sᶜ = {y : Space | ‖x‖ < ‖y‖} := by ext y; simp [S]
  have houter : (∫ y in Sᶜ, η y/‖y‖) ≤ (∫ y in Sᶜ, η y)/‖x‖ := by
    rw [← integral_div]
    apply integral_mono_ae
      ((CoulombAnalysis.tfPotential_integrable hη hp 0).congr (by filter_upwards [] with y; simp)).integrableOn
      (hη.div_const _).integrableOn
    filter_upwards [ae_restrict_mem hm.compl] with y hy
    exact div_le_div_of_nonneg_left (hn y) hx0 (le_of_lt (by simpa [S] using hy))
  rw [CoulombAnalysis.tfPotential_newton hη hp hr hR hs hx,← he]
  calc
    _ ≤ (∫ y in S, η y)/‖x‖ + (∫ y in Sᶜ, η y)/‖x‖ := add_le_add le_rfl houter
    _ = _ := by rw [← add_div,integral_add_compl hm hη]

lemma ae_ne_point (a : Space) : ∀ᵐ z : Space, z ≠ a := by
  rw [ae_iff]
  simp

lemma spatialSmearing_potential_le {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hnη : ∀ x, 0 ≤ η x)
    (hr : CoulombAnalysis.IsRadial η) (hηn : ∫ x : Space, η x = 1)
    (hmρ : Measurable ρ) (hρ : Integrable ρ) (hpρ : MemLp ρ (5/3 : ENNReal))
    (hnρ : ∀ x, 0 ≤ ρ x) (a : Space) :
    CoulombAnalysis.tfPotential (spatialSmearing η ρ) a ≤ CoulombAnalysis.tfPotential ρ a := by
  obtain ⟨R,hR,hS⟩ := hcη.isCompact.isBounded.exists_pos_norm_le
  have hs (y : Space) (hy : η y ≠ 0) : ‖y‖ ≤ R := hS y (subset_tsupport η hy)
  rw [spatialSmearing_potential hη hcη hmρ hρ]
  apply integral_mono_ae (smearing_potential_integrable hη hcη hmρ hρ a)
    (CoulombAnalysis.tfPotential_integrable hρ hpρ a)
  filter_upwards [ae_ne_point a] with z hz
  have hh := radial_potential_le_point (hη.integrable_of_hasCompactSupport hcη)
    (hη.memLp_of_hasCompactSupport hcη) hnη hr hR.le hs
    (x := a-z) (sub_ne_zero.mpr (Ne.symm hz))
  rw [hηn] at hh
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh (hnρ z)

lemma spatialSmearing_potential_eq {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hr : CoulombAnalysis.IsRadial η)
    (hηn : ∫ x : Space, η x = 1) (hmρ : Measurable ρ) (hρ : Integrable ρ)
    {R : ℝ} (hR : 0 < R) (hs : ∀ y, η y ≠ 0 → ‖y‖ ≤ R)
    (a : Space) (hsep : ∀ z, ρ z ≠ 0 → R ≤ ‖a-z‖) :
    CoulombAnalysis.tfPotential (spatialSmearing η ρ) a = CoulombAnalysis.tfPotential ρ a := by
  rw [spatialSmearing_potential hη hcη hmρ hρ]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : ρ z = 0
  · simp [hz]
  · rw [CoulombAnalysis.tfPotential_newton_exterior_closed
      (hη.integrable_of_hasCompactSupport hcη) (hη.memLp_of_hasCompactSupport hcη)
      hr hR hs (hsep z hz),hηn,mul_one_div]

end Work_RadialPacket_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

lemma coherentPacket_fderiv {g : Space → ℂ} (hg : Differentiable ℝ g) (z p x v : Space) :
    fderiv ℝ (coherentPacket g z p) x v =
      (fderiv ℝ g (x-z) v + g (x-z) * ((inner ℝ p v : ℂ) * Complex.I)) *
        Complex.exp ((inner ℝ p x : ℂ) * Complex.I) := by
  have hd := (hg (x-z)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
  have hp := ((Complex.ofRealCLM.comp (innerSL ℝ p)).hasFDerivAt (x := x)).mul_const Complex.I
  have hh := hd.mul hp.cexp
  rw [show fderiv ℝ (coherentPacket g z p) x = _ from hh.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,Complex.ofRealCLM_apply,innerSL_apply_apply,
    Function.comp_apply,id_eq]
  ring

lemma real_coherentPacket_derivative_sq {g : Space → ℝ} (hg : Differentiable ℝ g)
    (z p x v : Space) :
    ‖fderiv ℝ (coherentPacket (fun x => (g x : ℂ)) z p) x v‖^2 =
      (fderiv ℝ g (x-z) v)^2 + (g (x-z))^2 * (inner ℝ p v)^2 := by
  have hd : Differentiable ℝ (fun x => (g x : ℂ)) := Complex.ofRealCLM.differentiable.comp hg
  rw [coherentPacket_fderiv hd,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
  have he : fderiv ℝ (fun x => (g x : ℂ)) (x-z) v = (fderiv ℝ g (x-z) v : ℂ) := by
    exact congrArg (fun A : Space →L[ℝ] ℂ => A v)
      (Complex.ofRealCLM.hasFDerivAt.comp (x-z) (hg (x-z)).hasFDerivAt).fderiv
  rw [he,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

lemma real_coherentPacket_gradient_sq {g : Space → ℝ} (hg : Differentiable ℝ g)
    (z p x : Space) :
    (∑ a : Fin 3, ‖fderiv ℝ (coherentPacket (fun x => (g x : ℂ)) z p) x
      (EuclideanSpace.single a 1)‖^2) =
      (∑ a : Fin 3, (fderiv ℝ g (x-z) (EuclideanSpace.single a 1))^2) + (g (x-z))^2 * ‖p‖^2 := by
  simp_rw [real_coherentPacket_derivative_sq hg]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  congr 1
  congr 1
  rw [← sum_coordinate_sq]
  apply Finset.sum_congr rfl
  intro a _
  simp [EuclideanSpace.inner_single_right]

end CoulombAtom

end

end OAI
