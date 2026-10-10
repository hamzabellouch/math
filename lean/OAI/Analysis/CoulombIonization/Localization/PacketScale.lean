import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CoherentRealKinetic

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

def scaledRealPacket (b : ℝ) (g : Space → ℝ) (x : Space) : ℝ :=
  b ^ (-(3/2 : ℝ))*g (b⁻¹ • x)

lemma packetScale_factor {b : ℝ} (hb : 0 < b) :
    (b ^ (-(3/2 : ℝ)))^2*b^3 = 1 := by
  rw [← Real.rpow_mul_natCast hb.le,← Real.rpow_natCast b 3,← Real.rpow_add hb]
  norm_num

lemma scaledRealPacket_smooth (b : ℝ) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (scaledRealPacket b g) :=
  contDiff_const.mul (hg.comp (b⁻¹ • ContinuousLinearMap.id ℝ Space).contDiff)

lemma scaledRealPacket_compact {b : ℝ} (hb : 0 < b) {g : Space → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (scaledRealPacket b g) :=
  (hg.comp_smul (inv_ne_zero hb.ne')).mul_left

lemma scaledRealPacket_mass {b : ℝ} (hb : 0 < b) (g : Space → ℝ) :
    (∫ x : Space, (scaledRealPacket b g x)^2) = ∫ x : Space, (g x)^2 := by
  simp only [scaledRealPacket,mul_pow,integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x : Space => (g x)^2) hb.le,
    space_finrank,smul_eq_mul,← mul_assoc,packetScale_factor hb,one_mul]

lemma scaledRealPacket_derivative (b : ℝ) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (x v : Space) :
    fderiv ℝ (scaledRealPacket b g) x v =
      b ^ (-(3/2 : ℝ))*b⁻¹*fderiv ℝ g (b⁻¹ • x) v := by
  have hcomp : HasFDerivAt (fun y : Space => g (b⁻¹ • y))
      ((fderiv ℝ g (b⁻¹ • x)).comp (b⁻¹ • ContinuousLinearMap.id ℝ Space)) x :=
    ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
      (b⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have hh := hcomp.const_mul (b ^ (-(3/2 : ℝ)))
  rw [show scaledRealPacket b g = fun x => b ^ (-(3/2 : ℝ))*g (b⁻¹ • x) from rfl,hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  ring

lemma scaledRealPacket_dirichlet {b : ℝ} (hb : 0 < b) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) :
    packetDirichlet (scaledRealPacket b g) = packetDirichlet g / b^2 := by
  unfold packetDirichlet
  simp_rw [scaledRealPacket_derivative b hg,mul_pow,integral_const_mul]
  have hi (a : Fin 3) := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Space => (fderiv ℝ g x (EuclideanSpace.single a 1))^2) hb.le
  simp only [space_finrank,smul_eq_mul] at hi
  simp_rw [hi]
  have hc : (b ^ (-(3/2 : ℝ)))^2*b⁻¹^2*b^3 = (b^2)⁻¹ := by
    calc
      _ = ((b ^ (-(3/2 : ℝ)))^2*b^3)*b⁻¹^2 := by ring
      _ = _ := by rw [packetScale_factor hb,one_mul,inv_pow]
  simp only [← mul_assoc,hc,inv_mul_eq_div,Finset.sum_div]

lemma scaledRealPacket_radial (b : ℝ) {g : Space → ℝ} (hg : CoulombAnalysis.IsRadial g) :
    CoulombAnalysis.IsRadial (scaledRealPacket b g) := by
  intro x y hxy
  unfold scaledRealPacket
  rw [hg (b⁻¹ • x) (b⁻¹ • y) (by simp only [norm_smul,hxy])]

lemma scaledRealPacket_support {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) {x : Space} (hx : scaledRealPacket b g x ≠ 0) : ‖x‖ < b := by
  have hg : g (b⁻¹ • x) ≠ 0 := by intro hz; exact hx (by simp [scaledRealPacket,hz])
  have hb' := hs (subset_tsupport g hg)
  simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hb.le)] at hb'
  rwa [inv_mul_eq_div,div_lt_one hb] at hb'

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

theorem price_le_scaled_packet_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
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
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z) +
      (1/2:ℝ)*(∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖) -
      Z*CoulombAnalysis.tfPotential ρ 0 + lam*(∫ z, ρ z) + coreDensityInteraction ψ ρ := by
  have hrad : CoulombAnalysis.IsRadial (fun x => (scaledRealPacket b g x)^2) := by
    intro x y hxy
    dsimp only
    rw [scaledRealPacket_radial b hr x y hxy]
  have hnorm : (∫ x : Space, (scaledRealPacket b g x)^2) = 1 := by
    rw [scaledRealPacket_mass hpositive,hgn]
  have hh := price_le_radial_packet_insertion hψ hm hn hJ hs hb
    (scaledRealPacket_smooth b hg) (scaledRealPacket_compact hpositive hcg)
    hnorm hrad hpositive (fun y hy => (scaledRealPacket_support hpositive hgs hy).le)
    A hcore hsep hnuc hcs hZ hlam
  rw [scaledRealPacket_dirichlet hpositive hg] at hh
  convert hh using 1; ring

end CoulombAtom

end

end OAI
