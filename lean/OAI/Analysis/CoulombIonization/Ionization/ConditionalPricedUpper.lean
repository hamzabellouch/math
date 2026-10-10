import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CorePriceExcess
import OAI.Analysis.CoulombIonization.Ionization.PricedUpperComparison

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma coreCoulombAt_scale {N : ℕ} (c : ℝ) (ψ : FormVector N) (y : Space) :
    coreCoulombAt (scaleForm c ψ) y = c^2*coreCoulombAt ψ y := by
  simp only [coreCoulombAt,scaleForm,scaled_norm_sq,mul_div_assoc,integral_const_mul,←Finset.mul_sum]

lemma FormZeroAt.scale {N : ℕ} {ψ : FormVector N} {x : Configuration N}
    (hz : FormZeroAt ψ x) (c : ℝ) : FormZeroAt (scaleForm c ψ) x := by
  intro s
  constructor
  · change (c:ℂ)*ψ.value s x = 0
    rw [(hz s).1,mul_zero]
  · intro i a
    change (c:ℂ)*ψ.gradient s i a x = 0
    rw [(hz s).2,mul_zero]

lemma normalizedCoreField_eq_scaled {N : ℕ} (Z lam : ℝ) {ψ : FormVector N}
    (hm : 0 < formMass ψ) (y : Space) : normalizedCoreField Z lam ψ y =
      Z/‖y‖-lam-coreCoulombAt (scaleForm (Real.sqrt (formMass ψ))⁻¹ ψ) y := by
  rw [coreCoulombAt_scale,inv_pow,Real.sq_sqrt hm.le]
  unfold normalizedCoreField
  field_simp
  ring

theorem conditional_priced_patch_upper {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hpositive : 0 < b)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) J))
    (hnuc : ∀ z ∈ J, b ≤ ‖z‖) (hcs : ∀ a ∈ A, ∀ z ∈ J, b ≤ ‖a-z‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam*formMass ψ ≤ formEnergy Z ψ + lam*N*formMass ψ +
      formMass ψ * (tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) +
        (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z) -
        (∫ y : Space, normalizedCoreField Z lam ψ y * ρ y) +
        (1/2:ℝ)*(∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖)) := by
  rcases (formMass_nonneg ψ).eq_or_lt with hz | hmass
  · simpa only [←hz,mul_zero,zero_mul,add_zero] using hψ.priced_lower_bound hZ hlam
  · have hh := priced_patch_upper_comparison (hψ.normalize hmass) hm hn hJ hs hb hg hcg
      hgn hr hgs hpositive A (fun x i hi => (hcore x i hi).scale _) hsep hnuc hcs hZ hlam
    simp_rw [←normalizedCoreField_eq_scaled Z lam hmass] at hh
    have hh' := mul_le_mul_of_nonneg_right hh hmass.le
    rw [formEnergy_scale,inv_pow,Real.sq_sqrt hmass.le] at hh'
    refine hh'.trans_eq ?_
    field_simp
    ring

end CoulombAtom

end

end OAI
