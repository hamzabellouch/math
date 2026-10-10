import Mathlib
import OAI.Analysis.BiholderTransport.Volume.Measurable
import OAI.Analysis.BiholderTransport.Coordinates.ChartLipschitz
import OAI.Analysis.BiholderTransport.Coordinates.Inner
import OAI.Analysis.BiholderTransport.Convexity.CoordinateSemiconvex

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section CoordinateExpansion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma contDiffAt_exists_quadraticExpansion {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ u v, inner ℝ (A u) v=inner ℝ u (A v)) ∧ HasQuadraticExpansion f p A := by
  let J := (InnerProductSpace.toDual ℝ E).symm
  let p : E := J (fderiv ℝ f 0)
  let A : E →L[ℝ] E := J.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ f) 0)
  have hA (u v : E) : inner ℝ (A u) v=fderiv ℝ (fderiv ℝ f) 0 u v :=
    InnerProductSpace.toDual_symm_apply
  have hp (u : E) : inner ℝ p u=fderiv ℝ f 0 u := InnerProductSpace.toDual_symm_apply
  refine ⟨p,A,?_,?_⟩
  · intro u v
    have hc : inner ℝ u (A v)=inner ℝ (A v) u := real_inner_comm _ _
    rw [hA,hc,hA]
    exact (hf.isSymmSndFDerivAt (by norm_num)).eq u v
  · rw [hasQuadraticExpansion_iff_isLittleO]
    convert contDiffAt_second_order_remainder hf using 1
    funext h
    simp only [quadraticTaylor,hp,hA]
    ring

omit [CompleteSpace E] in
lemma HasQuadraticExpansion.of_isLittleO_sub {f g : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hg : HasQuadraticExpansion g p A) (h0 : f 0=g 0)
    (hfg : (fun h => f h-g h) =o[𝓝 0] (fun h : E => ‖h‖^2)) :
    HasQuadraticExpansion f p A := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hg ⊢
  convert! hfg.add hg using 1
  funext h
  rw [h0]
  ring

omit [CompleteSpace E] in
lemma HasQuadraticExpansion.congr_eventually {f g : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f p A) (hfg : f =ᶠ[𝓝 0] g) :
    HasQuadraticExpansion g p A := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hf ⊢
  apply hf.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hfg] with h hh
  rw [hh,hfg.self_of_nhds]

omit [CompleteSpace F] in
lemma HasQuadraticExpansion.comp_contDiffAt {f : F → ℝ} {p : F} {A : F →L[ℝ] F}
    (hf : HasQuadraticExpansion f p A) {η : E → F} (hη0 : η 0=0)
    (hη : ContDiffAt ℝ 2 η 0) :
    ∃ q : E, ∃ B : E →L[ℝ] E,
      (∀ u v, inner ℝ (B u) v=inner ℝ u (B v)) ∧
        HasQuadraticExpansion (fun h => f (η h)) q B := by
  let P : F → ℝ := quadraticTaylor (f 0) p A
  have hP : ContDiff ℝ 2 P := by
    dsimp [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  obtain ⟨q,B,hBs,hB⟩ := contDiffAt_exists_quadraticExpansion (hP.contDiffAt.comp 0 hη)
  refine ⟨q,B,hBs,hB.of_isLittleO_sub ?_ ?_⟩
  · simp only [Function.comp_apply,hη0,P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  · have hD := (hη.differentiableAt (by norm_num)).hasFDerivAt
    have hO : η =O[𝓝 0] (fun h : E => h) := by
      simpa only [hη0,sub_zero] using hD.isBigO_sub
    have hO2 : (fun h : E => ‖η h‖^2) =O[𝓝 0] (fun h : E => ‖h‖^2) := by
      simpa only [←sq] using hO.norm_norm.mul hO.norm_norm
    have ht : Tendsto η (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt,hη0] using hη.continuousAt
    exact ((hasQuadraticExpansion_iff_isLittleO.mp hf).comp_tendsto ht).trans_isBigO hO2

end CoordinateExpansion
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AENormalExpansion
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] in
lemma cTransform_ae_normal_quadraticExpansion {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ w ∂metricVolume (M := M) n,
      ∃ p : TangentSpace 𝓘(ℝ,Model n) w, ∃ A : TangentSpace 𝓘(ℝ,Model n) w →L[ℝ] TangentSpace 𝓘(ℝ,Model n) w,
        (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
        HasQuadraticExpansion (fun h => cTransform v (riemannianExp w h)) p A := by
  suffices HH : ∀ x∈(univ : Set M), ∃ U : Set M, IsOpen U ∧ x∈U ∧
      (∀ᵐ w ∂metricVolume (M := M) n, w∈U →
        ∃ p : TangentSpace 𝓘(ℝ,Model n) w, ∃ A : TangentSpace 𝓘(ℝ,Model n) w →L[ℝ] TangentSpace 𝓘(ℝ,Model n) w,
          (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
          HasQuadraticExpansion (fun h => cTransform v (riemannianExp w h)) p A) by
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
  let η := fun h : TangentSpace 𝓘(ℝ,Model n) w => d (riemannianExp w h)-d w
  have hη0 : η 0=0 := by simp [η,riemannianExp_zero]
  have hη : ContDiffAt ℝ ∞ η 0 := by
    have hc : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d w :=
      contMDiffAt_extChartAt' (by simpa only [d,extChartAt_source] using hwU.1)
    have hd := (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp w 0) from by
      simpa only [riemannianExp_zero] using hc).comp 0 (contMDiff_riemannianExp_fiber w 0)
    exact hd.contDiffAt.sub contDiffAt_const
  obtain ⟨q,B,hBs,hB⟩ := hQ.comp_contDiffAt hη0
    (hη.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  refine ⟨q,B,hBs,hB.congr_eventually ?_⟩
  have hsource : d.source∈𝓝 w := (isOpen_extChartAt_source x).mem_nhds hwU.1
  have hsource' : d.source∈𝓝 (riemannianExp (n := n) w 0) := by
    simpa only [riemannianExp_zero] using hsource
  have hnear := (contMDiff_riemannianExp_fiber (n := n) w).continuous.continuousAt.preimage_mem_nhds hsource'
  filter_upwards [hnear] with h hh
  have he : ψ (z+η h)=riemannianExp w h := by
    dsimp [ψ,z,η]
    rw [show d x+(d w-d x+(d (riemannianExp w h)-d w))=d (riemannianExp w h) by abel]
    exact d.left_inv hh
  exact congrArg (cTransform v) he

end AENormalExpansion
end WeakMTWTransport

end

end

end

end OAI
