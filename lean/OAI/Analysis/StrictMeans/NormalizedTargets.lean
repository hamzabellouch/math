import OAI.Analysis.StrictMeans.TransportBasic

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma upperArea_ne_zero : upperArea ≠ 0 := by
  intro h
  have he := coe_upperArea_preserving.map_eq
  rw [h,Measure.map_zero] at he
  have hh : (volume : Measure ℂ) {z | 0 < z.im} = 0 := by
    have hc := congrArg (fun ν : Measure ℂ => ν univ) he
    simpa using hc.symm
  have hp : 0 < (volume : Measure ℂ) {z | 0 < z.im} :=
    isOpen_halfPlane.measure_pos volume ⟨I,by simp⟩
  exact hp.ne' hh

lemma expected_source_mass (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (positive : Bool)
    {H : DiskFamily × UpperHalfPlane → ℝ≥0∞} (hH : Measurable H)
    (hcov : ∀ f z, H (f,z) = H (rebase f z,UpperHalfPlane.I)) (A : Set UpperHalfPlane) :
    (∫⁻ f, ∫⁻ z in A, sourceMassDensity β k f positive z * H (f,z) ∂upperArea
      ∂(μ : Measure DiskFamily)) =
      (∫⁻ z in A, ENNReal.ofReal (z.im⁻¹) ∂upperArea) *
        ∫⁻ f, ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) *
          H (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  have hm := (continuous_sourceMassDensity β k positive).measurable.mul hH
  rw [lintegral_lintegral_swap hm.aemeasurable]
  simp_rw [law_sourceMassDensity μ β k hlaw positive hH hcov]
  exact lintegral_mul_const _ (UpperHalfPlane.continuous_im.inv₀
    (fun z => z.im_ne_zero)).measurable.ennreal_ofReal

def badSourceTest (k : ℝ) : DiskFamily × UpperHalfPlane → ℝ≥0∞ :=
  (sourcePairingDomain k)ᶜ.indicator (fun _ => 1)

lemma measurable_badSourceTest {k : ℝ} (hk : 0 < k) : Measurable (badSourceTest k) :=
  measurable_const.indicator (measurableSet_sourcePairingDomain hk).compl

lemma badSourceTest_rebase (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    badSourceTest k (f,z) = badSourceTest k (rebase f z,UpperHalfPlane.I) := by
  classical
  have he := sourcePairingDomain_rebase_iff k f z UpperHalfPlane.I
  rw [affineProduct_I] at he
  simp only [badSourceTest,Set.indicator,mem_compl_iff,he]

lemma good_targets_bad_source_mass_zero {β k : ℝ} (hk : 0 < k) (f : DiskFamily)
    (hg : ∀ᵐ ξ : ℂ, GoodPair k (f,ξ)) :
    (∫⁻ z, sourceMassDensity β k f true z * badSourceTest k (f,z) ∂upperArea) = 0 := by
  have hm : Measurable (fun z : UpperHalfPlane => badSourceTest k (f,z)) :=
    (measurable_badSourceTest hk).comp (measurable_const.prodMk measurable_id)
  simp_rw [mul_comm (sourceMassDensity β k f true _) (badSourceTest k _)]
  rw [upper_source_area_formula hk.ne' f true hm]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hg] with ξ hξ
  unfold fiberSum
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  have hz := z.2.1
  have hp : 0 < z.1.im := hz.1
  have hD : (f,halfPlaneProjection z.1)∈sourcePairingDomain k := by
    rw [halfPlaneProjection_of_pos hp,sourcePairingDomain_eq_good_positive hk]
    refine ⟨?_,hz.2⟩
    rw [z.2.2]
    exact hξ
  simp [badSourceTest,hD]

lemma affine_law_base_good (μ : ProbabilityMeasure DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hlaw : AffineProbabilityLaw μ β) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) *
      badSourceTest ((β+2)/3) (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) = 0 := by
  let k := (β+2)/3
  have hk : 0 < k := by dsimp [k]; linarith
  have hz : (∫⁻ f, ∫⁻ z, sourceMassDensity β k f true z * badSourceTest k (f,z)
      ∂upperArea ∂(μ : Measure DiskFamily)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [affine_law_ae_good_pairs μ β hβ hlaw] with f hf
    exact good_targets_bad_source_mass_zero hk f hf
  have he := expected_source_mass μ β k hlaw true (measurable_badSourceTest hk)
    (badSourceTest_rebase k) univ
  simp only [Measure.restrict_univ] at he
  rw [he] at hz
  rcases mul_eq_zero.mp hz with ha | hb
  · have hm : Measurable (fun z : UpperHalfPlane=>ENNReal.ofReal (z.im⁻¹)) :=
      (UpperHalfPlane.continuous_im.inv₀ (fun z=>z.im_ne_zero)).measurable.ennreal_ofReal
    have hz0 := (lintegral_eq_zero_iff' hm.aemeasurable).mp ha
    let : NeZero upperArea := ⟨upperArea_ne_zero⟩
    obtain ⟨z,hz⟩ := hz0.exists
    exact False.elim ((ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr z.im_pos)) hz)
  · exact hb

end
end StrictInverseFirstPower

end

end OAI
