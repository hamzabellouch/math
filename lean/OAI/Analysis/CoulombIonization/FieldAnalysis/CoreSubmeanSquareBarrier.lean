import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.OuterFieldMaximum
import OAI.Analysis.CoulombIonization.Variational.WeightedCauchy
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.CoreSubmeanBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom
open CoulombAnalysis

lemma normalizedCoreField_pos_le {N : ℕ} (ψ : FormVector N)
    {Z lam d : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d)
    {z : Space} (hz : d ≤ ‖z‖) :
    max (normalizedCoreField Z lam ψ z) 0 ≤ Z/d := by
  apply max_le
  · exact (normalizedCoreField_le_nuclear ψ hZ hlam z).trans
      (div_le_div_of_nonneg_left hZ hd hz)
  · exact div_nonneg hZ hd.le

lemma positive_core_pair_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {η : Space → ℝ} (hη : Integrable η)
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z)
    {Z lam d : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d)
    (hs : ∀ z, η z ≠ 0 → d ≤ ‖z‖) (k : ℕ) :
    Integrable (fun z => (max (normalizedCoreField Z lam ψ z) 0)^k*η z) := by
  apply (hη.const_mul ((Z/d)^k)).mono'
    (((normalizedCoreField_measurable hψ Z lam).max measurable_const).pow_const k |>.mul hm).aestronglyMeasurable
  apply ae_of_all; intro z
  change ‖(max (normalizedCoreField Z lam ψ z) 0)^k*η z‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (le_max_right _ _) _) (hn z))]
  by_cases he : η z = 0
  · simp only [he,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_max_right _ _) (normalizedCoreField_pos_le ψ hZ hlam hd (hs z he)) k) (hn z)

theorem normalizedCoreField_radial_submean_sq {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hR : 0 < R) (hn : ∀ x, 0 ≤ η x)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y : Space) (hnuc : 2*R ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (max (normalizedCoreField Z lam ψ y) 0)^2 ≤
      ∫ z, (max (normalizedCoreField Z lam ψ z) 0)^2*η (z-y) := by
  let k := translatedDensity η y
  have hkm : Measurable k := translatedDensity_measurable hm y
  have hks : Function.support k ⊆ closedBall y R := translatedDensity_support hs y
  have hkb : ∀ z, |k z| ≤ B := fun z => hb (z-y)
  have hki : Integrable k := bounded_compact_integrable hkm (isCompact_closedBall _ _) hks hkb
  have hkn (z : Space) : 0 ≤ k z := hn (z-y)
  have hk1 : ∫ z, k z = 1 := (translatedDensity_mass η y).trans h1
  have hsep : ∀ z, k z ≠ 0 → R ≤ ‖z‖ := by
    intro z hz
    have hz0 := hs (z-y) hz
    have htri : ‖y‖ ≤ ‖z-y‖+‖z‖ := by
      calc
        ‖y‖ = ‖z-(z-y)‖ := by congr 1; abel
        _ ≤ ‖z‖+‖z-y‖ := norm_sub_le _ _
        _ = ‖z-y‖+‖z‖ := add_comm _ _
    linarith
  have hf1 : Integrable (fun z => max (normalizedCoreField Z lam ψ z) 0*k z) := by
    simpa only [pow_one] using positive_core_pair_integrable hψ hki hkm hkn hZ hlam hR hsep 1
  have hf2 := positive_core_pair_integrable hψ hki hkm hkn hZ hlam hR hsep 2
  have hh := normalizedCoreField_radial_submean hψ hm hR hn hs hb hr h1 y (by linarith) Z lam
  have hp : max (normalizedCoreField Z lam ψ y) 0 ≤
      ∫ z, max (normalizedCoreField Z lam ψ z) 0*k z := by
    apply max_le
    · apply hh.trans
      exact integral_mono (normalizedCoreField_pair_integrable hψ hkm (isCompact_closedBall _ _) hks hkb Z lam)
        hf1 (fun z => mul_le_mul_of_nonneg_right (le_max_left _ _) (hkn z))
    · exact integral_nonneg (fun z => mul_nonneg (le_max_right _ _) (hkn z))
  have hc := weighted_sum_integral_cauchy (ι := Unit) (X := fun _ => Space)
    (fun _ => volume) (fun _ => k) (fun _ z => max (normalizedCoreField Z lam ψ z) 0)
    (fun _ _ => 1) (fun _ => hkn) (fun _ => hf2)
    (fun _ => by simpa only [one_pow,one_mul] using hki)
    (fun _ => by simpa only [mul_one] using hf1)
  simp only [Finset.univ_unique,Finset.sum_singleton,one_pow,one_mul,mul_one,hk1,Real.sqrt_one] at hc
  have hi : 0 ≤ ∫ z, (max (normalizedCoreField Z lam ψ z) 0)^2*k z :=
    integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (hkn z))
  have hb0 := (sq_le_sq₀ (le_max_right _ _) (Real.sqrt_nonneg _)).mpr (hp.trans hc)
  rwa [Real.sq_sqrt hi] at hb0

end CoulombAtom

end

end OAI
