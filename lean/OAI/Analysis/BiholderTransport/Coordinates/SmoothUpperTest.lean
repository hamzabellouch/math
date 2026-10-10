import Mathlib
import OAI.Analysis.BiholderTransport.Volume.Measurable
import OAI.Analysis.BiholderTransport.CostGeometry.UpperTest
import OAI.Analysis.BiholderTransport.Convexity.CoordinateSemiconvex

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport

lemma HasQuadraticExpansion.smooth_upper_test
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {p : E} {A : E →L[ℝ] E} (h : HasQuadraticExpansion f p A) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P 0=f 0 ∧ ∀ᶠ z in 𝓝 0, f z≤P z := by
  let P := fun z => quadraticTaylor (f 0) p A z+‖z‖^2
  have hP : ContDiff ℝ ∞ P := by
    dsimp [P,quadraticTaylor]
    exact ((contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)).add (contDiff_norm_sq ℝ)
  refine ⟨P,hP,by simp [P,quadraticTaylor],?_⟩
  obtain ⟨r,hr,hR⟩ := h 1 zero_lt_one
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with z hz
  have H := (abs_le.mp (hR z (by simpa using hz))).2
  dsimp [P]
  linarith

section AEUpperTest
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma cTransform_ae_normal_smooth_upper_test {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ w ∂metricVolume (M := M) n,
      ∃ φ : TangentSpace 𝓘(ℝ,Model n) w → ℝ, ContDiffAt ℝ 2 φ 0 ∧
        φ 0=cTransform v w ∧
        ∀ᶠ h in 𝓝 0, cTransform v (riemannianExp w h)≤φ h := by
  suffices HH : ∀ x∈(univ : Set M), ∃ U : Set M, IsOpen U ∧ x∈U ∧
      (∀ᵐ w ∂metricVolume (M := M) n, w∈U →
        ∃ φ : TangentSpace 𝓘(ℝ,Model n) w → ℝ, ContDiffAt ℝ 2 φ 0 ∧
          φ 0=cTransform v w ∧
          ∀ᶠ h in 𝓝 0, cTransform v (riemannianExp w h)≤φ h) by
    simpa only [mem_univ,true_implies] using ae_of_locally_ae (metricVolume (M := M) n) HH
  intro x _
  obtain ⟨C,r,hr,htarget,hLip⟩ := exists_lipschitz_inverse_chart (n := n) x
  let d := extChartAt 𝓘(ℝ,Model n) x
  let ψ := fun z : Model n => d.symm (d x+z)
  have hψ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ ψ 0 := by
    apply (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d.symm (d x+0) from by
      simpa only [add_zero] using (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).comp
    exact (contDiff_const.add contDiff_id).contDiffAt.contMDiffAt
  obtain ⟨R,hR,K,hK,hconv⟩ := cTransform_uniform_smooth_coordinate_semiconvex hψ
  let B := ball (0:Model n) (min R r)
  let U := d.source ∩ (fun w => d w-d x) ⁻¹' B
  have hU : IsOpen U := ((continuousOn_extChartAt x).sub continuousOn_const).isOpen_inter_preimage
    (isOpen_extChartAt_source x) isOpen_ball
  refine ⟨U,hU,⟨mem_extChartAt_source x,by simpa [B] using And.intro hR hr⟩,?_⟩
  have hBtarget : ∀ z∈B, d x+z∈d.target := by
    intro z hz
    apply htarget
    change d x+z∈ball (d x) r
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using
      Metric.ball_subset_ball (min_le_right R r) hz
  have hB' : ∀ z∈B, d x+z∈ball (d x) r := by
    intro z hz
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using
      Metric.ball_subset_ball (min_le_right R r) hz
  have hψLip : LipschitzOnWith C ψ B := by
    intro a ha b hb
    simpa only [ψ,edist_dist,dist_eq_norm,add_sub_add_left_eq_sub] using
      hLip (hB' a ha) (hB' b hb)
  let μ : Measure (Model n) := Measure.hausdorffMeasure (n:ℝ)
  have hdim : Module.finrank ℝ (Model n)=n := by simp [Model]
  have : μ.IsAddHaarMeasure := by
    dsimp only [μ]
    rw [←hdim]
    infer_instance
  have hc : ConvexOn ℝ B (fun z => cTransform v (ψ z)+(2*K)/2*‖z‖^2) := by
    simpa only [mul_div_cancel_left₀ K (show (2:ℝ)≠0 by norm_num)] using
      (hconv v hv).subset (Metric.ball_subset_ball (min_le_left R r)) (convex_ball _ _)
  have hAlex := ConvexProximal.ae_quadraticExpansion_semiconvex_open (2*K) isOpen_ball hc μ
  let N := {z : Model n | z∈B ∧ ¬∃ p : Model n, ∃ A : Model n →L[ℝ] Model n,
    (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => cTransform v (ψ (z+h))) p A}
  have hN : μ N=0 := by
    apply measure_mono_null _ (ae_iff.mp hAlex)
    intro z hz
    exact fun hh => hz.2 (hh hz.1)
  have hImage : (Measure.hausdorffMeasure (n:ℝ) : Measure M) (ψ '' N)=0 := by
    apply le_antisymm _ (show (0:ℝ≥0∞)≤_ from zero_le)
    have hNsub : N⊆B := fun _ h => h.1
    have H := (hψLip.mono hNsub).hausdorffMeasure_image_le
      (d := (n:ℝ)) (by positivity)
    change _≤(C : ℝ≥0∞)^(n:ℝ)*μ N at H
    simpa only [hN,mul_zero] using H
  have hImageVol : metricVolume (M := M) n (ψ '' N)=0 := by
    simp only [metricVolume,Measure.smul_apply,smul_eq_mul,hImage,mul_zero]
  have hOutside : ∀ᵐ w ∂metricVolume (M := M) n, w∉ψ '' N := ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hImageVol)
  filter_upwards [hOutside] with w hw hwU
  let z := d w-d x
  have hzB : z∈B := hwU.2
  have hψz : ψ z=w := by simp only [ψ,z,add_sub_cancel,d.left_inv hwU.1]
  have hzN : z∉N := fun h => hw ⟨z,h,hψz⟩
  have hzQ : ∃ p : Model n, ∃ A : Model n →L[ℝ] Model n,
      (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
        HasQuadraticExpansion (fun h => cTransform v (ψ (z+h))) p A := by
    by_contra hh
    exact hzN ⟨hzB,hh⟩
  obtain ⟨p,A,_,hQ⟩ := hzQ
  obtain ⟨P,hP,hP0,hPup⟩ := hQ.smooth_upper_test
  let η := fun h : TangentSpace 𝓘(ℝ,Model n) w => d (riemannianExp w h)-d w
  have hη0 : η 0=0 := by simp [η,riemannianExp_zero]
  have hη : ContDiffAt ℝ ∞ η 0 := by
    have hc : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d w :=
      contMDiffAt_extChartAt' (by simpa only [d,extChartAt_source] using hwU.1)
    have hd := (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp w 0) from by
      simpa only [riemannianExp_zero] using hc).comp 0 (contMDiff_riemannianExp_fiber w 0)
    exact hd.contDiffAt.sub contDiffAt_const
  refine ⟨P ∘ η,?_,?_,?_⟩
  · exact ((hP.contDiffAt.comp 0 hη).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  · simpa only [Function.comp_apply,hη0,add_zero,hψz] using hP0
  · have hsource : d.source∈𝓝 w := (isOpen_extChartAt_source x).mem_nhds hwU.1
    have hsource' : d.source∈𝓝 (riemannianExp (n := n) w 0) := by
      simpa only [riemannianExp_zero] using hsource
    have hnear := (contMDiff_riemannianExp_fiber (n := n) w).continuous.continuousAt.preimage_mem_nhds hsource'
    have hPnear : ∀ᶠ h in 𝓝 0, cTransform v (ψ (z+η h))≤P (η h) :=
      (show Tendsto η (𝓝 0) (𝓝 0) by simpa only [ContinuousAt,hη0] using hη.continuousAt).eventually hPup
    filter_upwards [hnear,hPnear] with h hh hPh
    have he : ψ (z+η h)=riemannianExp w h := by
      dsimp [ψ,z,η]
      rw [show d x+(d w-d x+(d (riemannianExp w h)-d w))=d (riemannianExp w h) by abel]
      exact d.left_inv hh
    simpa only [Function.comp_apply,he] using hPh

lemma cTransform_ae_active_before_cut {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ x ∂metricVolume (M := M) n, ∀ p∈activeLogs (n := n) v x,
      p∈injectivityDomain x := by
  filter_upwards [cTransform_ae_mdifferentiableAt hv,cTransform_ae_normal_smooth_upper_test hv]
    with x hx htest
  obtain ⟨φ,hφ,hφ0,hup⟩ := htest
  exact fun p hp => active_before_cut_of_differentiable_upper_test hv hx hφ hφ0 hup hp

end AEUpperTest
end WeakMTWTransport

end

end

end

end OAI
