import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.ConditionalPricedUpper
import OAI.Analysis.CoulombIonization.FieldAnalysis.CoreFieldRegularity
import OAI.Analysis.CoulombIonization.Variational.PatchTranslatedDensity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff ENNReal

namespace CoulombAtom
open CoulombAnalysis

theorem conditional_priced_patch_minimizer_upper {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) (R : ℝ) (Φ : TFField R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hΦ : Φ =ᵐ[ballMeasure R] fun x => normalizedCoreField Z lam ψ (y+x))
    {F : ℝ} (hF : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    priceEnergy (energy Z) lam*formMass ψ ≤ formEnergy Z ψ+lam*N*formMass ψ+
      formMass ψ*(tfPatchFunctional R tfKinetic Φ f+
        (packetDirichlet g/2)*b⁻¹^2*(∫ x, f x ∂ballMeasure R)) := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
  let B := (max F 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)
  have hf : NonnegDensity f := tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos Φ
  have hB : ∀ᵐ x ∂ballMeasure R, f x ≤ B := tfPatchMinimizer_ae_bound tfKinetic_pos Φ hF
  have hh := conditional_priced_patch_upper hψ (translatedPatchDensity_measurable y R B f)
    (translatedPatchDensity_nonneg y R B f) (isCompact_closedBall y R)
    (translatedPatchDensity_support y R B f) (translatedPatchDensity_le y R B f)
    hg hcg hgn hr hgs hb A hcore hsep hnuc hcs hZ hlam
  rw [translatedPatchDensity_mass y hf hB,translatedPatchDensity_kinetic y hf hB,
    translatedPatchDensity_coulomb y hf hB,translatedPatchDensity_field y hf hB] at hh
  have he : (∫ x, normalizedCoreField Z lam ψ (y+x)*f x ∂ballMeasure R) =
      ∫ x, Φ x*f x ∂ballMeasure R := by
    apply integral_congr_ae
    filter_upwards [hΦ] with x hx
    rw [hx]
  rw [he] at hh
  simpa only [tfPatchFunctional,tfPatchLinear_apply,sub_eq_add_neg,add_assoc,
    add_left_comm,add_comm] using hh

theorem actual_core_patch_minimizer_upper {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) (R : ℝ)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    let hfield := normalizedCoreField_memLp_patch hψ.sobolevVector A hcore y R hb hb hnuc hcs Z lam
    let Φ := hfield.toLp (fun x => normalizedCoreField Z lam ψ (y+x))
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    priceEnergy (energy Z) lam*formMass ψ ≤ formEnergy Z ψ+lam*N*formMass ψ+
      formMass ψ*(tfPatchFunctional R tfKinetic Φ f+
        (packetDirichlet g/2)*b⁻¹^2*(∫ x, f x ∂ballMeasure R)) := by
  dsimp only
  let hfield := normalizedCoreField_memLp_patch hψ.sobolevVector A hcore y R hb hb hnuc hcs Z lam
  have hbound : ∀ᵐ x ∂ballMeasure R,
      hfield.toLp (fun x => normalizedCoreField Z lam ψ (y+x)) x ≤ |Z|/b+|lam|+N/b := by
    filter_upwards [hfield.coeFn_toLp,ae_restrict_mem measurableSet_ball] with x hx hmem
    rw [hx]
    have hz : y+x ∈ closedBall y R := by
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using
        (show ‖x‖ ≤ R from (by simpa only [mem_ball,dist_eq_norm,sub_zero] using hmem : ‖x‖ < R).le)
    exact (le_abs_self _).trans (normalizedCoreField_abs_le hψ.sobolevVector A hcore hb
      (y+x) (fun a ha => hcs a ha _ hz) hb (hnuc _ hz) Z lam)
  exact conditional_priced_patch_minimizer_upper hψ y R _ hZ hlam hfield.coeFn_toLp hbound
    hg hcg hgn hr hgs hb A hcore hsep hnuc hcs

end CoulombAtom

end

end OAI
