import Mathlib
import OAI.Analysis.Conductivity.Sobolev.LocalPiolaFlux

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
namespace ScalarConductivity

lemma contDiff_clm_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun L : E →L[ℝ] E => L.det) := by
  classical
  let b := Module.finBasis ℝ E
  simp_rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply',
    LinearMap.toMatrix_apply]
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  change ContDiff ℝ n (fun L : E →L[ℝ] E => (b.coord (σ i)).toContinuousLinearMap (L (b i)))
  exact (b.coord (σ i)).toContinuousLinearMap.contDiff.comp ((ContinuousLinearMap.apply ℝ E (b i)).contDiff)

lemma contDiff_of_contDiffOn_tsupport {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {n : WithTop ℕ∞} {f : E → V} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n f s) (hfS : tsupport f ⊆ s) : ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt (hs.mem_nhds (hfS hx))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

lemma localPiolaFlux_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (F : E → E) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ X.source) : ContDiff ℝ (↑(⊤ : ℕ∞)) (localPiolaFlux X F) := by
  apply contDiff_of_contDiffOn_tsupport X.open_target _ (localPiolaFlux_tsupport X F hc hs)
  apply X.open_target.contDiffOn_iff.mpr
  intro y hy
  have hxi := hXi.contDiffAt (X.open_target.mem_nhds hy)
  have hx := hX.contDiffAt (X.open_source.mem_nhds (X.map_target hy))
  have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun z => fderiv ℝ X (X.symm z)) y :=
    (hx.fderiv_right (by simp)).comp y hxi
  have hd0 : (fderiv ℝ X (X.symm y)).det ≠ 0 :=
    local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) (X.map_target hy)
  have hdet := ((contDiff_clm_det (E := E) (↑(⊤ : ℕ∞))).contDiffAt.comp y hd).abs hd0
  have hformula := (hdet.inv (abs_ne_zero.mpr hd0)).smul
    (hd.clm_apply (hF.contDiffAt.comp y hxi))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [X.open_target.mem_nhds hy] with z hz
  simp [localPiolaFlux, hz]

lemma exists_smooth_extension_near_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (φ : E → ℝ) (hφ : ContDiffOn ℝ (↑(⊤ : ℕ∞)) φ U) :
    ∃ g : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] φ := by
  obtain ⟨χ, hχ₀, hχ₁, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hK.isClosed
      (disjoint_left.mpr (fun x hx hxK => hx (hKU hxK))) (n := ⊤)
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  refine ⟨fun x => χ x * φ x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hφ.contDiffAt (hU.mem_nhds hx))
    · have hzero : ∀ᶠ z in 𝓝 x, χ z = 0 := hχ₀.filter_mono (nhds_le_nhdsSet hx)
      apply (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun _ : E => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [hzero] with z hz
      simp [hz]
  · intro x hx
    have hone : ∀ᶠ z in 𝓝 x, χ z = 1 := hχ₁.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hone] with z hz
    simp [hz]

lemma compactFlux_local_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (μ : Measure E) {U : Set E} (hU : IsOpen U)
    (F : E → E) (hc : HasCompactSupport F) (hs : tsupport F ⊆ U)
    (hF : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0)
    (φ : E → ℝ) (hφ : ContDiffOn ℝ (↑(⊤ : ℕ∞)) φ U) :
    (∫ x, fderiv ℝ φ x (F x) ∂μ) = 0 := by
  obtain ⟨g, hg, hge⟩ := exists_smooth_extension_near_compact hU hc hs φ hφ
  rw [← hF g hg]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport F
  · rw [(hge x hx).fderiv_eq]
  · rw [image_eq_zero_of_notMem_tsupport hx, map_zero, map_zero]

lemma localPiolaFlux_zero_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (F : E → E) (hc : HasCompactSupport F) (hs : tsupport F ⊆ X.source)
    (hF : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    (∫ y, fderiv ℝ ψ y (localPiolaFlux X F y) ∂μ) = 0 := by
  rw [localPiolaFlux_pairing μ X (hX.differentiableOn (by simp))
    (fun _ hx => local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) hx)
    F (subset_closure.trans hs) ψ (hψ.differentiable (by simp))]
  exact compactFlux_local_test μ X.open_source F hc hs hF _ (hψ.comp_contDiffOn hX)

end ScalarConductivity

end

end OAI
