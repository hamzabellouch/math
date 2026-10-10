import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CorePriceExcess
import OAI.Analysis.CoulombIonization.FieldAnalysis.CoreFieldPairing
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedSmear

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombAnalysis

lemma normalizedCoreField_pair_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) (Z lam : ℝ) :
    Integrable (fun y => normalizedCoreField Z lam ψ y*ρ y) := by
  have h1 := bounded_compact_integrable hm hJ hs hb
  have hp := bounded_compact_memLp hm hJ hs hb (5/3 : ENNReal)
  have hn : Integrable (fun y : Space => ρ y/‖y‖) := by
    simpa only [zero_sub,norm_neg] using tfPotential_integrable h1 hp 0
  have hc := coreDensityField_integrable hψ hm hJ hs hb
  have hh := (((hn.const_mul (Z*formMass ψ)).sub hc).div_const (formMass ψ)).sub (h1.const_mul lam)
  apply hh.congr
  filter_upwards [] with y
  simp only [normalizedCoreField,Pi.sub_apply]
  ring

lemma normalizedCoreField_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) (Z lam : ℝ) :
    (∫ y, normalizedCoreField Z lam ψ y*ρ y) =
      (Z*formMass ψ*tfPotential ρ 0-coreDensityInteraction ψ ρ)/formMass ψ-
        lam*(∫ y, ρ y) := by
  have h1 := bounded_compact_integrable hm hJ hs hb
  have hp := bounded_compact_memLp hm hJ hs hb (5/3 : ENNReal)
  have hn : Integrable (fun y : Space => ρ y/‖y‖) := by
    simpa only [zero_sub,norm_neg] using tfPotential_integrable h1 hp 0
  have hc := coreDensityField_integrable hψ hm hJ hs hb
  have he (y : Space) : normalizedCoreField Z lam ψ y*ρ y =
      (Z*formMass ψ*(ρ y/‖y‖)-ρ y*coreCoulombAt ψ y)/formMass ψ-lam*ρ y := by
    unfold normalizedCoreField
    ring
  simp_rw [he]
  rw [integral_sub (f := fun y => (Z*formMass ψ*(ρ y/‖y‖)-ρ y*coreCoulombAt ψ y)/formMass ψ)
    (g := fun y => lam*ρ y) (((hn.const_mul (Z*formMass ψ)).sub hc).div_const _) (h1.const_mul lam),
    integral_div,integral_sub (f := fun y => Z*formMass ψ*(ρ y/‖y‖))
      (g := fun y => ρ y*coreCoulombAt ψ y) (hn.const_mul (Z*formMass ψ)) hc,
    integral_const_mul,integral_const_mul,←coreDensityInteraction_eq_field hψ hm hJ hs hb]
  simp only [tfPotential,zero_sub,norm_neg]

lemma radial_translatedDensity_potential {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hR : 0 < R) (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R)
    (hb : ∀ x, |η x| ≤ B) (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y z : Space) (hz : R ≤ ‖z-y‖) :
    tfPotential (translatedDensity η y) z = 1/‖z-y‖ := by
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hs x hx
  rw [potential_translatedDensity,
    tfPotential_newton_exterior_closed
      (bounded_compact_integrable hm (isCompact_closedBall _ _) hsupport hb)
      (bounded_compact_memLp hm (isCompact_closedBall _ _) hsupport hb (5/3 : ENNReal))
      hr hR hs hz,h1]

lemma radial_translatedDensity_core {N : ℕ} (ψ : FormVector N)
    {η : Space → ℝ} (hm : Measurable η) {R B : ℝ} (hR : 0 < R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (hc : ∀ a ∈ A, R ≤ ‖a-y‖) :
    coreDensityInteraction ψ (translatedDensity η y) = coreCoulombAt ψ y := by
  unfold coreDensityInteraction coreCoulombAt
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hi : x i ∈ A
  · rw [radial_translatedDensity_potential hm hR hs hb hr h1 y (x i) (hc _ hi),mul_one_div]
  · rw [(hcore x i hi s).1]
    simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,zero_div]

lemma normalizedCoreField_radial_average {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {η : Space → ℝ} (hm : Measurable η) {R B : ℝ} (hR : 0 < R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (hn : R ≤ ‖y‖) (hc : ∀ a ∈ A, R ≤ ‖a-y‖) (Z lam : ℝ) :
    (∫ z, normalizedCoreField Z lam ψ z*η (z-y)) = normalizedCoreField Z lam ψ y := by
  change (∫ z, normalizedCoreField Z lam ψ z*translatedDensity η y z) = _
  rw [normalizedCoreField_pairing hψ (translatedDensity_measurable hm y)
    (isCompact_closedBall y R) (translatedDensity_support hs y) (fun z => hb (z-y)),
    radial_translatedDensity_core ψ hm hR hs hb hr h1 A hcore y hc,
    radial_translatedDensity_potential hm hR hs hb hr h1 y 0 (by simpa only [zero_sub,norm_neg] using hn),
    translatedDensity_mass,h1,zero_sub,norm_neg,mul_one,mul_one_div]
  rfl

end CoulombAtom
namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

theorem retainedSmear_core_field {N M : ℕ} {ψ : FormVector M} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Finset (Fin N)) (x : Configuration N)
    (A : Set Space) (hcore : ∀ u i, u i ∉ A → FormZeroAt ψ u)
    (hn : ∀ i ∈ S, Real.sqrt 3*b ≤ ‖x i‖)
    (hc : ∀ i ∈ S, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-x i‖) (Z lam : ℝ) :
    (∫ z, normalizedCoreField Z lam ψ z*retainedSmear b S x z) =
      ∑ i ∈ S, normalizedCoreField Z lam ψ (x i) := by
  have haB (z : Space) : |varthetaScaled b z| ≤ b⁻¹^3 := by
    rw [abs_of_nonneg (varthetaScaled_nonneg hb z)]
    exact varthetaScaled_le hb z
  simp only [retainedSmear,Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i hi => normalizedCoreField_radial_average hψ
      (varthetaScaled_measurable b) (by positivity) (varthetaScaled_support_bound hb) haB
      (fun _ _ h => varthetaScaled_radial b h) (integral_varthetaScaled hb)
      A hcore (x i) (hn i hi) (hc i hi) Z lam)
  · intro i _
    exact normalizedCoreField_pair_integrable hψ
      (translatedDensity_measurable (varthetaScaled_measurable b) (x i))
      (isCompact_closedBall _ _) (translatedDensity_support (varthetaScaled_support_bound hb) (x i))
      (fun z => haB (z-x i)) Z lam

end CoulombNeumann

end

end OAI
