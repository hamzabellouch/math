import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy
import OAI.Geometry.PrescribedRicci.KahlerIntegration

namespace OAI

/-! Integrated Kahler Energy. -/

section

 

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma determinant_eq_volume (g : KaehlerMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (g.matrix i z).det = (g.volumeCoefficient i z : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.pos_iff.mp (g.positive i z hz).det_pos).2.symm

lemma holRealDeriv_zero_off_support {q : Coordinates d → ℝ} {z : Coordinates d}
    (hz : z ∉ tsupport q) : holRealDeriv q z = 0 := by
  have hd : fderiv ℝ q z = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hz (tsupport_fderiv_subset ℝ h))
  funext j
  simp only [holRealDeriv, hd, map_zero, Pi.zero_apply]

lemma integral_real_cofactor (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {q : Coordinates d → ℝ} (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) (hs : tsupport q ⊆ (A.chart i).target) :
    (∫ z, q z * g.volumeCoefficient i z * ((g.matrix i z)⁻¹ * φ.hessian i z).trace.re) =
      -(∫ z, g.volumeCoefficient i z *
        (gradientPair (g.matrix i z) (holRealDeriv q z) (holRealDeriv (φ.localExpression i) z)).re) := by
  let qc : Coordinates d → ℂ := fun z => (q z : ℂ)
  have hqc : ContDiff ℝ ∞ qc := Complex.ofRealCLM.contDiff.comp hq
  have hcc : HasCompactSupport qc := hc.comp_left Complex.ofReal_zero
  have hsc : tsupport qc ⊆ (A.chart i).target := (tsupport_comp_subset Complex.ofReal_zero q).trans hs
  have hd (j : Fin d) : ∀ z ∈ tsupport qc,
      ContDiffAt ℝ ∞ (fun y => g.cofactorFlux φ i y j) z :=
    fun z hz => g.contDiffAt_cofactorFlux φ i (hsc hz) j
  let F := fun z => qc z * ((g.matrix i z).det * ((g.matrix i z)⁻¹ * φ.hessian i z).trace)
  let G := fun z => ∑ j, barDeriv qc z j * g.cofactorFlux φ i z j
  have hF : Integrable F := by
    have hh := integrable_finsetSum Finset.univ (fun j _ => integrable_mul_barDeriv_local hqc (hd j) hcc j)
    apply hh.congr (Filter.Eventually.of_forall _)
    intro z
    simp only [← Finset.mul_sum]
    by_cases hz : z ∈ tsupport qc
    · rw [g.cofactorFlux_divergence φ i (hsc hz)]
    · simp only [F, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hG : Integrable G := integrable_finsetSum Finset.univ
    (fun j _ => integrable_barDeriv_mul_local hqc (hd j) hcc j)
  have he := congrArg Complex.re (g.integral_cofactorFlux φ i hqc hcc hsc)
  have hFe : ∀ z, (F z).re = q z * g.volumeCoefficient i z *
      ((g.matrix i z)⁻¹ * φ.hessian i z).trace.re := by
    intro z
    by_cases hz : z ∈ tsupport q
    · simp only [F, qc, g.determinant_eq_volume i (hs hz), Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im,
        add_zero]
      ring
    · simp only [F, qc, image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero,
        zero_mul, Complex.zero_re]
  have hGe : ∀ z, (G z).re = g.volumeCoefficient i z *
      (gradientPair (g.matrix i z) (holRealDeriv q z) (holRealDeriv (φ.localExpression i) z)).re := by
    intro z
    have hb : ∀ j, barDeriv qc z j = star (holRealDeriv q z j) :=
      fun j => barDeriv_ofReal (hq.differentiable (by simp) z) j
    have hc' : G z = (g.matrix i z).det *
        gradientPair (g.matrix i z) (holRealDeriv q z) (holRealDeriv (φ.localExpression i) z) := by
      simp only [G, cofactorFlux, hb, MongeAmpere.weightedInverse, Matrix.smul_apply,
        smul_eq_mul, gradientPair, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hc']
    by_cases hz : z ∈ tsupport q
    · rw [g.determinant_eq_volume i (hs hz)]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    · rw [holRealDeriv_zero_off_support hz]
      simp only [gradientPair, Pi.zero_apply, star_zero, mul_zero, zero_mul,
        Finset.sum_const_zero, Complex.zero_re]
  change (∫ z, F z).re = (-(∫ z, G z)).re at he
  have hrF := Complex.reCLM.integral_comp_comm hF
  have hrG := Complex.reCLM.integral_comp_comm hG
  change (∫ z, (F z).re) = (∫ z, F z).re at hrF
  change (∫ z, (G z).re) = (∫ z, G z).re at hrG
  rw [← hrF, Complex.neg_re, ← hrG] at he
  simpa only [hFe, hGe] using he

lemma chart_energy_identity [T2Space X] [CompactSpace X] (g : KaehlerMetric A)
    (ψ φ : SmoothRealFunction A) (i : Fin A.count)
    (hs : tsupport ψ.value ⊆ (A.chart i).source) :
    g.chartIntegral i (fun x => ψ.value x * (g.laplacian φ).value x) =
      -g.chartIntegral i (g.energy ψ φ).value := by
  obtain ⟨hq, hc, ht⟩ := ψ.localized_smooth_compact i hs
  have he := g.integral_real_cofactor φ i hq hc ht
  have hl : (fun z => ψ.localized i z * g.volumeCoefficient i z *
      ((g.matrix i z)⁻¹ * φ.hessian i z).trace.re) =
      (A.chart i).target.indicator (fun z =>
        ψ.value ((A.chart i).symm z) * (g.laplacian φ).value ((A.chart i).symm z) *
          g.volumeCoefficient i z) := by
    funext z
    by_cases hz : z ∈ (A.chart i).target
    · rw [Set.indicator_of_mem hz, ψ.localized_eq hz]
      have hp := g.laplacian_localExpression φ i hz
      change (g.laplacian φ).value ((A.chart i).symm z) = _ at hp
      rw [hp]
      change _ * _ * _ = _ * ((g.matrix i z)⁻¹ * φ.hessian i z).trace.re * _
      dsimp only [SmoothRealFunction.localExpression, Function.comp_apply]
      ring
    · simp only [SmoothRealFunction.localized, ite_eq_right hz, Set.indicator_of_notMem hz, zero_mul]
  have hr : (fun z => g.volumeCoefficient i z *
      (gradientPair (g.matrix i z) (holRealDeriv (ψ.localized i) z)
        (holRealDeriv (φ.localExpression i) z)).re) =
      (A.chart i).target.indicator (fun z => (g.energy ψ φ).value ((A.chart i).symm z) *
        g.volumeCoefficient i z) := by
    funext z
    by_cases hz : z ∈ (A.chart i).target
    · rw [Set.indicator_of_mem hz]
      have hloc : ψ.localized i =ᶠ[𝓝 z] ψ.localExpression i := by
        filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy using ψ.localized_eq hy
      have hd : holRealDeriv (ψ.localized i) z = holRealDeriv (ψ.localExpression i) z := by
        funext j
        unfold holRealDeriv
        rw [hloc.fderiv_eq]
      rw [hd]
      have hh := g.energy_local ψ φ i hz
      change (g.energy ψ φ).value ((A.chart i).symm z) = _ at hh
      rw [hh, mul_comm]
    · rw [Set.indicator_of_notMem hz, holRealDeriv_zero_off_support (fun h => hz (ht h))]
      simp only [gradientPair, Pi.zero_apply, star_zero, mul_zero, zero_mul,
        Finset.sum_const_zero, Complex.zero_re]
  rw [hl, hr, integral_indicator (A.chart i).open_target.measurableSet,
    integral_indicator (A.chart i).open_target.measurableSet] at he
  exact he

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
