import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketScale
import OAI.Analysis.CoulombIonization.FieldAnalysis.CoreFieldPairing

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma priced_core_field_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) (Z lam : ℝ) :
    (∫ y : Space, (Z/‖y‖-lam-coreCoulombAt ψ y)*ρ y) =
      Z*CoulombAnalysis.tfPotential ρ 0-lam*(∫ y, ρ y)-coreDensityInteraction ψ ρ := by
  have h1 := bounded_compact_integrable hm hJ hs hb
  have hp := bounded_compact_memLp hm hJ hs hb (5/3 : ENNReal)
  have hn : Integrable (fun y : Space => ρ y/‖y‖) := by
    simpa only [zero_sub,norm_neg] using CoulombAnalysis.tfPotential_integrable h1 hp 0
  have hc := coreDensityField_integrable hψ hm hJ hs hb
  have he (y : Space) : (Z/‖y‖-lam-coreCoulombAt ψ y)*ρ y =
      Z*(ρ y/‖y‖)-lam*ρ y-ρ y*coreCoulombAt ψ y := by ring
  simp_rw [he]
  have hi := integral_sub ((hn.const_mul Z).sub (h1.const_mul lam)) hc
  simp only [Pi.sub_apply] at hi
  rw [hi]
  have hi' := integral_sub (hn.const_mul Z) (h1.const_mul lam)
  rw [hi',integral_const_mul,integral_const_mul,
    ← coreDensityInteraction_eq_field hψ hm hJ hs hb]
  simp only [CoulombAnalysis.tfPotential,zero_sub,norm_neg]

theorem priced_patch_upper_comparison {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hpositive : 0 < b)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) J))
    (hnuc : ∀ z ∈ J, b ≤ ‖z‖) (hcs : ∀ a ∈ A, ∀ z ∈ J, b ≤ ‖a-z‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam*N +
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z) -
      (∫ y : Space, (Z/‖y‖-lam-coreCoulombAt ψ y)*ρ y) +
      (1/2:ℝ)*(∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖) := by
  have hab : ∀ z, |ρ z| ≤ B := fun z => by rw [abs_of_nonneg (hn z)]; exact hb z
  rw [priced_core_field_pairing hψ.sobolevFermion.sobolevVector hm hJ hs hab]
  have hh := price_le_scaled_packet_insertion hψ hm hn hJ hs hb hg hcg hgn hr hgs hpositive
    A hcore hsep hnuc hcs hZ hlam
  linarith

end CoulombAtom

end

end OAI
