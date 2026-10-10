import OAI.Analysis.StrictMeans.TransportInjection

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def upperBox (S a b : ℝ) : Set UpperHalfPlane := UpperHalfPlane.coe ⁻¹' complexBox S a b

lemma measurableSet_upperBox (S a b : ℝ) : MeasurableSet (upperBox S a b) :=
  UpperHalfPlane.measurable_coe (measurableSet_complexBox S a b)

lemma lintegral_upperBox_inv {S a b : ℝ} (hS : 0 ≤ S) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ z in upperBox S a b, ENNReal.ofReal (z.im⁻¹) ∂upperArea) =
      ENNReal.ofReal (2*S*(Real.log b-Real.log a)) := by
  have hm : Measurable (fun z : UpperHalfPlane => ENNReal.ofReal (z.im⁻¹)) :=
    UpperHalfPlane.continuous_im.measurable.inv.ennreal_ofReal
  rw [← lintegral_indicator (measurableSet_upperBox S a b),
    upperArea_lintegral (hm.indicator (measurableSet_upperBox S a b))]
  have he : (∫⁻ z in {z : ℂ | 0 < z.im},
      (upperBox S a b).indicator (fun w => ENNReal.ofReal (w.im⁻¹)) (halfPlaneProjection z)) =
      ∫⁻ z in {z : ℂ | 0 < z.im},
      (complexBox S a b).indicator (fun w => ENNReal.ofReal (w.im⁻¹)) z := by
    apply setLIntegral_congr_fun isOpen_halfPlane.measurableSet
    intro z hz
    dsimp only
    rw [halfPlaneProjection_of_pos hz]
    rfl
  rw [he,lintegral_indicator (measurableSet_complexBox S a b),
    Measure.restrict_restrict (measurableSet_complexBox S a b),inter_eq_left.mpr]
  · exact lintegral_complexBox_inv hS ha hab
  · intro z hz
    exact ha.trans_le hz.2.1

lemma partner_mem_expanded_box {k N S Y : ℝ} (hN : 1 ≤ N) (_hY : 1 ≤ Y)
    (f : DiskFamily) {z : UpperHalfPlane} (hz : z∈upperBox S 1 Y)
    (hD : (f,z)∈truncatedPairingDomain k N) :
    sourcePartner k (f,z)∈upperBox (S+N*Y) (1/N) (N*Y) := by
  change |(sourcePartner k (f,z)).re| ≤ S+N*Y ∧
    1/N ≤ (sourcePartner k (f,z)).im ∧ (sourcePartner k (f,z)).im ≤ N*Y
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  change |z.re| ≤ S ∧ 1 ≤ z.im ∧ z.im ≤ Y at hz
  have hylo := (le_div_iff₀ z.im_pos).mp hD.2.1
  have hyhi := (div_le_iff₀ z.im_pos).mp hD.2.2.1
  refine ⟨?_,?_,hyhi.trans (mul_le_mul_of_nonneg_left hz.2.2 hN0.le)⟩
  · calc
      |(sourcePartner k (f,z)).re| = |(sourcePartner k (f,z)).re-z.re+z.re| := by ring_nf
      _ ≤ |(sourcePartner k (f,z)).re-z.re| + |z.re| := abs_add_le _ _
      _ ≤ N*z.im+S := add_le_add hD.2.2.2 hz.1
      _ ≤ S+N*Y := by nlinarith [hz.2.2]
  · nlinarith [one_div_pos.mpr hN0]

lemma box_transport_expectation (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) {k N S Y : ℝ} (hk : 0 < k)
    (hβ : 3*(k-1)=β-1) (hN : 1 ≤ N) (hS : 0 < S) (hY : 1 < Y) :
    ENNReal.ofReal (2*S*Real.log Y) *
      (∫⁻ f, ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
        transportTest k N (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) ≤
      ENNReal.ofReal (2*(S+N*Y)*(Real.log Y+2*Real.log N)) *
        ∫⁻ f, ENNReal.ofReal (jacobianPart k f false UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  have hi := lintegral_mono (μ := (μ : Measure DiskFamily)) (fun f =>
    transport_set_inequality hk hβ f (measurableSet_upperBox S 1 Y)
      (measurableSet_upperBox (S+N*Y) (1/N) (N*Y))
      (fun _ hz hD => partner_mem_expanded_box hN hY.le f hz hD))
  have hR := expected_source_mass μ β k hlaw false (H := fun _ => 1)
    measurable_const (fun _ _ => rfl) (upperBox (S+N*Y) (1/N) (N*Y))
  simp only [mul_one] at hR
  rw [expected_source_mass μ β k hlaw true (measurable_transportTest hk N)
    (transportTest_rebase hk N),hR,lintegral_upperBox_inv hS.le zero_lt_one hY.le] at hi
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hY0 : 0 < Y := lt_trans zero_lt_one hY
  have hlo : 1/N ≤ N*Y := by
    apply (div_le_iff₀ hN0).mpr
    have hNY : 1 ≤ N*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hY.le)]
    simpa using mul_le_mul hNY hN (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0≤N*Y)
  rw [lintegral_upperBox_inv (by positivity) (one_div_pos.mpr hN0) hlo,
    Real.log_one,sub_zero,Real.log_mul hN0.ne' hY0.ne',Real.log_div one_ne_zero hN0.ne',
    Real.log_one] at hi
  convert hi using 1
  congr 2
  ring

end
end StrictInverseFirstPower

end

end OAI
