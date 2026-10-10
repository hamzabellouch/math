import OAI.Analysis.CircleDomains.Topology.PlanarFilledJump
import OAI.Analysis.CircleDomains.Sobolev.LocalGradientMajorant
import OAI.Analysis.CircleDomains.Sobolev.VerticalFilledDerivative

namespace OAI

/-! The finite-disk distributional estimate in the second coordinate,
obtained by the measure-preserving interchange of the two axes. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem planar_filled_vertical_jump
    {I : Type*} [Fintype I] (c : I → ℂ) (r value A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {L : ℝ} (hL : 0 < L) (hsub : ∀ i, closedBall (c i) (r i) ⊆ ball 0 L)
    {v F G : ℂ → ℝ}
    (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    (he : IntegrableOn (euclideanGradientEnergy v) (⋃ i, closedBall (c i) (r i))ᶜ)
    (hF : EqOn F (clipScalar ∘ v) (⋃ i, closedBall (c i) (r i))ᶜ)
    (hfill : ∀ i, EqOn F (fun _ => clipScalar (value i)) (closedBall (c i) (r i)))
    (hcluster : ∀ i p t, p ∈ closedBall (c i) (r i) →
      MapClusterPt t (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v → |t - value i| ≤ A i)
    (hrep : ∀ᵐ z ∂(volume : Measure ℂ), deriv (F ∘ verticalLine z.re) z.im = G z)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball 0 L)
    (hint : Integrable (fun z => F z * fderiv ℝ φ z Complex.I))
    (hdint : Integrable (fun z => G z * φ z))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, |φ z| ≤ C) :
    |(∫ z, F z * fderiv ℝ φ z Complex.I) + (∫ z, G z * φ z)| ≤
      4 * C * ∑ i, r i * A i := by
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let V := (⋃ i, closedBall (axisSwap (c i)) (r i))ᶜ
  have hswap : MeasurePreserving axisSwap (volume : Measure ℂ) volume := axisSwap.measurePreserving
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun _ => isClosed_closedBall).isOpen_compl
  have hVU : V = axisSwap ⁻¹' U := by
    simp only [V, U, preimage_compl, preimage_iUnion, axisSwap_preimage_closedBall]
  have hV : IsOpen V := hVU ▸ hU.preimage axisSwap.continuous
  have hvV : ContDiffOn ℝ 1 (v ∘ axisSwap) V := by
    rw [hVU]
    exact hv.comp axisSwap.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  have heV : IntegrableOn (euclideanGradientEnergy (v ∘ axisSwap)) V := by
    rw [hVU]
    exact (integral_energy_axisSwap hU hv he).1
  obtain ⟨ρ, hρ, hmajor⟩ := exists_integrable_gradient_majorant_on_square hV heV hL.le
  have hdisjV : Pairwise (Disjoint on fun i => closedBall (axisSwap (c i)) (r i)) := by
    intro i j hij
    simpa only [axisSwap_preimage_closedBall] using (hdisj hij).preimage axisSwap
  have hball (i : I) {z : ℂ} (hz : z ∈ closedBall (axisSwap (c i)) (r i)) :
      axisSwap z ∈ closedBall (c i) (r i) := by
    change z ∈ axisSwap ⁻¹' closedBall (c i) (r i)
    rwa [axisSwap_preimage_closedBall]
  have hsubV (i : I) : closedBall (axisSwap (c i)) (r i) ⊆ ball 0 L := by
    intro z hz
    have hb := hsub i (hball i hz)
    simpa only [mem_ball, dist_zero_right, axisSwap.norm_map] using hb
  have hFV : EqOn (F ∘ axisSwap) (clipScalar ∘ (v ∘ axisSwap)) V := by
    intro z hz
    apply hF
    change z ∈ axisSwap ⁻¹' U
    rw [← hVU]
    exact hz
  have hfillV (i : I) : EqOn (F ∘ axisSwap) (fun _ => clipScalar (value i))
      (closedBall (axisSwap (c i)) (r i)) := fun z hz => hfill i (hball i hz)
  have hclusterV : ∀ i p t, p ∈ closedBall (axisSwap (c i)) (r i) →
      MapClusterPt t (𝓝[V] p) (v ∘ axisSwap) → |t - value i| ≤ A i := by
    intro i p t hp ht
    apply hcluster i (axisSwap p) t (hball i hp)
    apply MapClusterPt.of_comp _ ht
    rw [hVU]
    exact tendsto_nhdsWithin_iff.mpr
      ⟨axisSwap.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
  have hrepV : ∀ᵐ z ∂(volume : Measure ℂ),
      deriv ((F ∘ axisSwap) ∘ horizontalLine z.im) z.re = (G ∘ axisSwap) z := by
    filter_upwards [hswap.quasiMeasurePreserving.ae hrep] with z hz
    have hf : (F ∘ axisSwap) ∘ horizontalLine z.im = F ∘ verticalLine z.im := by
      funext x
      simp only [comp_apply, axisSwap_horizontalLine]
    simpa only [hf, axisSwap_re, axisSwap_im, comp_apply] using hz
  have hφd (z : ℂ) : fderiv ℝ (φ ∘ axisSwap) z 1 =
      fderiv ℝ φ (axisSwap z) Complex.I := by
    have hd := ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp z
      axisSwap.hasFDerivAt).fderiv
    rw [hd]
    change fderiv ℝ φ (axisSwap z) (axisSwap 1) = _
    rw [axisSwap_one]
  have hsV : tsupport (φ ∘ axisSwap) ⊆ ball 0 L := by
    intro z hz
    have hb := hsupp (tsupport_comp_subset_preimage φ axisSwap.continuous hz)
    simpa only [mem_ball, dist_zero_right, axisSwap.norm_map] using hb
  have hiV : Integrable (fun z => (F ∘ axisSwap) z * fderiv ℝ (φ ∘ axisSwap) z 1) := by
    simp only [comp_apply, hφd]
    exact hswap.integrable_comp_of_integrable hint
  have hgV : Integrable (fun z => (G ∘ axisSwap) z * (φ ∘ axisSwap) z) :=
    hswap.integrable_comp_of_integrable hdint
  have h := planar_filled_horizontal_jump_of_density (fun i => axisSwap (c i)) r value A
    hr hA hdisjV hL hsubV hvV hρ hmajor hFV hfillV hclusterV hrepV
    (hφ.comp axisSwap.toContinuousLinearEquiv.contDiff) hsV hiV hgV hC
    (fun z => hbound (axisSwap z))
  change |(∫ z, (F ∘ axisSwap) z * fderiv ℝ (φ ∘ axisSwap) z 1) +
    (∫ z, (G ∘ axisSwap) z * (φ ∘ axisSwap) z)| ≤ _ at h
  simp_rw [hφd] at h
  simp only [comp_apply] at h
  have he₁ : (∫ z, F (axisSwap z) * fderiv ℝ φ (axisSwap z) Complex.I) =
      ∫ z, F z * fderiv ℝ φ z Complex.I := hswap.integral_comp axisSwap.toMeasurableEquiv.measurableEmbedding (fun z : ℂ => F z * fderiv ℝ φ z Complex.I)
  have he₂ : (∫ z, G (axisSwap z) * φ (axisSwap z)) =
      ∫ z, G z * φ z := hswap.integral_comp axisSwap.toMeasurableEquiv.measurableEmbedding (fun z : ℂ => G z * φ z)
  rw [he₁, he₂] at h
  exact h

end CircleDomainRigidity

end OAI
