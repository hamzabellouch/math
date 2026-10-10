import Mathlib
import OAI.Geometry.CubicTorus.Estimates.InteriorBallSubset

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem forced_cmc_linearized_holder_gradient {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    {B : Plane → Plane} (hB : Continuous B) {DB : ℝ} (hDB : 0≤DB)
    (hBHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖B x-B y‖≤DB*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))=0) :
    ∃ H : Plane → Plane,∃ s K β : ℝ,0<s ∧ s≤R/4 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
      ContinuousOn H (Metric.ball 0 s) ∧
      H =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (G : Plane → Plane) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (H x) (H y)≤K*(dist x y)^β := by
  obtain ⟨r,C,γ,hr,hC,hγ,hγ1,hosc⟩ := forced_cmc_uniform_oscillation hp hpb hR hα hα1 hD hDB hHolder u G hB hBHolder hg hd
  let s := min (R/4) (r/4)
  have hs : 0<s := lt_min (by positivity) (by positivity)
  have hsR : s≤R/4 := min_le_left _ _
  have hsr : 4*s≤r := by have := min_le_right (R/4) (r/4); dsimp [s]; linarith
  have hh : ∀ x∈Metric.ball (0 : Plane) s,∀ ρ : ℝ,0<ρ → ρ≤r → ∃ q : Plane,
      (∫ y in Metric.ball x ρ,‖G y-q‖^2)≤C*ρ^(2+2*(γ/2)) := by
    intro x hx ρ hρ hρr
    simpa only [mul_div_cancel₀ γ (by norm_num : (2:ℝ)≠0)] using
      hosc x ((Metric.ball_subset_ball hsR) hx) ρ hρ hρr
  obtain ⟨H,K,hK,hHc,hHe,hHp⟩ := plane_campanato_regularity G hr hC (half_pos hγ) hs hsr hh
  exact ⟨H,s,K,γ/2,hs,hsR,hK,half_pos hγ,by linarith,hHc,hHe,hHp⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma compact_probability_average_integrable [NormedSpace ℝ F] [CompleteSpace F] {f : Plane → F}
    (hf : Continuous f) (hc : HasCompactSupport f) (b : ContDiffBump (0 : Plane)) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) := by
  obtain ⟨C,hC,hbound⟩ := continuous_compact_norm_bound hf hc
  exact Integrable.of_bound (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    C (Eventually.of_forall fun y ↦ hbound (x-y))

lemma compact_probability_average_uniform {f : Plane → F}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoUniformly (fun i x ↦ ∫ y,f (x-y) ∂graphSmoothingMeasure (graphMollifier i)) f atTop := by
  have hu : UniformContinuous f := hf.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hu (ε/2) (half_pos hε)
  filter_upwards [graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hδ)] with i hi x
  have hfi := compact_probability_average_integrable hf hc (graphMollifier i) x
  have he : (∫ _y : Plane,f x ∂graphSmoothingMeasure (graphMollifier i))=f x := by simp
  rw [dist_comm,dist_eq_norm,← he,← integral_sub hfi (integrable_const _)]
  calc
    _ ≤ ∫ _y : Plane,ε/2 ∂graphSmoothingMeasure (graphMollifier i) :=
      norm_integral_le_of_norm_le (integrable_const _) (by
        filter_upwards [graphSmoothingMeasure_radius (graphMollifier i)] with y hy
        have hd : dist (x-y) x<δ := by
          simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hy.trans_lt hi
        simpa only [dist_eq_norm] using (hclose hd).le)
    _ < ε := by simp; linarith

omit [CompleteSpace F] in
lemma vector_graphSmooth_eq_convolution [CompleteSpace F] (b : ContDiffBump (0 : Plane)) (f : Plane → F) :
    (fun x ↦ ∫ y,f (x-y) ∂graphSmoothingMeasure b)=
      b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f := by
  funext x
  rw [graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _),convolution_def,ContinuousLinearMap.lsmul_apply]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma test_kernel_support {R : ℝ} {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2))
    (b : ContDiffBump (0 : Plane)) (hb : b.rOut<R/2) :
    tsupport (fun y ↦ b.normed volume (x-y))⊆Metric.ball 0 R := by
  have hs : tsupport (fun y ↦ b.normed volume (x-y))⊆
      (fun y ↦ x-y) ⁻¹' tsupport (b.normed volume) :=
    tsupport_comp_subset_preimage (f := fun y : Plane ↦ x-y) (b.normed volume)
      ((continuous_const : Continuous (fun _ : Plane ↦ x)).sub continuous_id)
  intro y hy
  have hh := hs hy
  have he : tsupport (b.normed (volume : Measure Plane))=Metric.closedBall 0 b.rOut :=
    b.tsupport_normed_eq
  change x-y∈tsupport (b.normed volume) at hh
  rw [he,Metric.mem_closedBall,dist_zero_right] at hh
  have hx' : ‖x‖<R/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  change dist y 0<R
  rw [dist_zero_right]
  calc
    ‖y‖ = ‖x-(x-y)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖x‖+‖x-y‖ := norm_sub_le _ _
    _ < R/2+R/2 := add_lt_add hx' (hh.trans_lt hb)
    _ = R := by ring

lemma PlaneWeakGradient.smooth_hasFDerivAt {R : ℝ} {f : Plane → ℝ} {G : Plane → Plane}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hG : Continuous G) (hGc : HasCompactSupport G)
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    (b : ContDiffBump (0 : Plane)) (hb : b.rOut<R/2)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2)) :
    HasFDerivAt (graphSmooth b f)
      ((InnerProductSpace.toDual ℝ Plane) (∫ y,G (x-y) ∂graphSmoothingMeasure b)) x := by
  have hfi : Integrable f (volume : Measure Plane) := hf.integrable_of_hasCompactSupport hfc
  have he : graphSmooth b f=f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] b.normed volume := by
    rw [graphSmooth_eq_convolution]
    exact real_convolution_comm _ _
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
    rw [he]
    exact b.hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hfi.locallyIntegrable b.contDiff_normed
  apply (hsm.differentiable (by simp)).differentiableAt.hasFDerivAt.congr_fderiv
  ext v
  rw [he,fderiv_compact_convolution hfi.locallyIntegrable b.contDiff_normed b.hasCompactSupport_normed,
    convolution_mul]
  have hw' := hw v (fun y ↦ b.normed volume (x-y))
    (b.contDiff_normed.comp (contDiff_const.sub contDiff_id))
    (b.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x))
    (test_kernel_support hx b hb)
  have hder (y : Plane) : fderiv ℝ (fun z ↦ b.normed volume (x-z)) y v=
      -(fderiv ℝ (b.normed volume) (x-y) v) := by
    have hbn : Differentiable ℝ (b.normed (volume : Measure Plane)) :=
      (b.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))).differentiable (by simp)
    have ht := hbn.differentiableAt.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    have he := ht.fderiv
    dsimp only [Function.comp_def,id_eq] at he
    rw [he]
    simp
  simp_rw [hder,mul_neg,integral_neg,neg_neg] at hw'
  rw [← hw']
  change (∫ y,⟪G y,v⟫*b.normed volume (x-y))=⟪∫ y,G (x-y) ∂graphSmoothingMeasure b,v⟫
  have hie : (∫ y,⟪G (x-y),v⟫ ∂graphSmoothingMeasure b)=
      ⟪∫ y,G (x-y) ∂graphSmoothingMeasure b,v⟫ := by
    simpa only [real_inner_comm] using
      integral_inner (compact_probability_average_integrable hG hGc b x) v
  rw [← hie]
  rw [graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _),smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun y ↦ b.normed volume y*⟪G (x-y),v⟫)
    (volume : Measure Plane) x]
  simp only [sub_sub_cancel]
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ mul_comm _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.compact_hasFDerivAt {R : ℝ} {f : Plane → ℝ} {G : Plane → Plane}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hG : Continuous G) (hGc : HasCompactSupport G)
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2)) :
    HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x := by
  have hR : 0<R/2 := Metric.nonempty_ball.mp ⟨x,hx⟩
  have hGu := (InnerProductSpace.toDual ℝ Plane).isometry.uniformContinuous.comp_tendstoUniformly
    (compact_probability_average_uniform hG hGc)
  apply hasFDerivAt_of_tendstoUniformlyOnFilter (f := fun i ↦ graphSmooth (graphMollifier i) f) (g := f)
    (hGu.tendstoUniformlyOnFilter.mono_right le_top)
  · apply Filter.Eventually.prod_mk
      (graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hR))
      (Metric.isOpen_ball.mem_nhds hx) |>.mono
    rintro ⟨i,y⟩ ⟨hi,hy⟩
    exact hw.smooth_hasFDerivAt hf hfc hG hGc (graphMollifier i) hi hy
  · exact Eventually.of_forall fun y ↦ compact_probability_average_uniform hf hfc |>.tendsto_at y

lemma PlaneWeakGradient.continuous_hasFDerivAt {R : ℝ} (hR : 0<R)
    {f : Plane → ℝ} {G : Plane → Plane}
    (hf : ContinuousOn f (Metric.ball 0 R)) (hG : ContinuousOn G (Metric.ball 0 R))
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/4)) :
    HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f' : Plane → ℝ := fun y ↦ b y*f y
  let G' : Plane → Plane := fun y ↦ b y • G y
  have hf' : Continuous f' := continuous_local_cutoff Metric.isOpen_ball hf b.continuous hbs
  have hG' : Continuous G' := continuous_local_vector_cutoff Metric.isOpen_ball hG b.continuous hbs
  have he (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/2)) : b y=1 :=
    b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hw' : PlaneWeakGradient (Metric.ball 0 (R/2)) f' G' :=
    (hw.mono (Metric.ball_subset_ball (by linarith))).local_congr measurableSet_ball
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with y hy; simp [f',he y hy])
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with y hy; simp [G',he y hy])
  have hx' : x∈Metric.ball (0 : Plane) ((R/2)/2) := by
    have he : (R/2)/2=R/4 := by ring
    rwa [he]
  have hh := hw'.compact_hasFDerivAt hf' b.hasCompactSupport.mul_right hG'
    b.hasCompactSupport.smul_right hx'
  have hx2 : x∈Metric.ball (0 : Plane) (R/2) :=
    (Metric.ball_subset_ball (by linarith : R/4≤R/2)) hx
  have hloc : f'=ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx2] with y hy
    simp [f',he y hy]
  have heG : G' x=G x := by simp [G',he x hx2]
  rw [heG] at hh
  exact hh.congr_of_eventuallyEq hloc.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma linear_cmc_source_holder {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {p B : Plane → Plane} {LA : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y)))
    {R α DA DB Dg : ℝ} (hDA : 0≤DA) (hDB : 0≤DB) (hDg : 0≤Dg)
    (hAd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ (fun z ↦ cmcJacobian (p z)) x) (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y)≤DA*(dist x y)^α)
    (hBd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ B x) (fderiv ℝ B y)≤DB*(dist x y)^α)
    (hgd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤Dg*(dist x y)^α)
    {v : Plane} (hv : ‖v‖≤1) {x y : Plane} (hx : x∈Metric.ball (0 : Plane) R)
    (hy : y∈Metric.ball (0 : Plane) R) :
    ‖(fderiv ℝ B x v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) x v (gradient g x))-
      (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))‖≤
        (DB+DA*(K:ℝ)+(LA:ℝ)*Dg)*(dist x y)^α := by
  let A := fun z ↦ cmcJacobian (p z)
  have hb' : ‖fderiv ℝ B x v-fderiv ℝ B y v‖≤DB*(dist x y)^α := by
    calc
      _ = ‖(fderiv ℝ B x-fderiv ℝ B y) v‖ := rfl
      _ ≤ ‖fderiv ℝ B x-fderiv ℝ B y‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (DB*(dist x y)^α)*1 := mul_le_mul (by simpa only [dist_eq_norm] using hBd x hx y hy) hv
        (norm_nonneg _) (mul_nonneg hDB (Real.rpow_nonneg (dist_nonneg) _))
      _ = _ := mul_one _
  have hAd' : ‖fderiv ℝ A x-fderiv ℝ A y‖≤DA*(dist x y)^α := by
    have hh := hAd x hx y hy
    rw [dist_eq_norm (fderiv ℝ (fun z ↦ cmcJacobian (p z)) x : Plane →L[ℝ] Plane →L[ℝ] Plane)
      (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y : Plane →L[ℝ] Plane →L[ℝ] Plane)] at hh
    exact hh
  have ha' : ‖fderiv ℝ A x v-fderiv ℝ A y v‖≤DA*(dist x y)^α := by
    calc
      _ = ‖(fderiv ℝ A x-fderiv ℝ A y) v‖ := rfl
      _ ≤ ‖fderiv ℝ A x-fderiv ℝ A y‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (DA*(dist x y)^α)*1 := mul_le_mul hAd' hv
        (norm_nonneg _) (mul_nonneg hDA (Real.rpow_nonneg (dist_nonneg) _))
      _ = _ := mul_one _
  have hag : ‖fderiv ℝ A y v‖≤(LA:ℝ) :=
    ((fderiv ℝ A y).le_opNorm v).trans
      ((mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hA) hv (norm_nonneg _) LA.coe_nonneg).trans_eq (mul_one _))
  have hgx : ‖gradient g x‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hgd' : ‖gradient g x-gradient g y‖≤Dg*(dist x y)^α := by
    rw [← dist_eq_norm,plane_gradient_dist]; exact hgd x hx y hy
  have hEq : fderiv ℝ A x v (gradient g x)-fderiv ℝ A y v (gradient g y)=
      (fderiv ℝ A x v-fderiv ℝ A y v) (gradient g x)+fderiv ℝ A y v (gradient g x-gradient g y) := by
    simp only [sub_apply,map_sub]; abel
  have he : ‖fderiv ℝ A x v (gradient g x)-fderiv ℝ A y v (gradient g y)‖≤
      (DA*(K:ℝ)+(LA:ℝ)*Dg)*(dist x y)^α := by
    rw [hEq]
    calc
      _ ≤ ‖(fderiv ℝ A x v-fderiv ℝ A y v) (gradient g x)‖+
          ‖fderiv ℝ A y v (gradient g x-gradient g y)‖ := norm_add_le _ _
      _ ≤ (DA*(dist x y)^α)*(K:ℝ)+(LA:ℝ)*(Dg*(dist x y)^α) := add_le_add
        (((fderiv ℝ A x v-fderiv ℝ A y v).le_opNorm _).trans
          (mul_le_mul ha' hgx (norm_nonneg _) (mul_nonneg hDA (Real.rpow_nonneg dist_nonneg _))))
        (((fderiv ℝ A y v).le_opNorm _).trans
          (by simpa only [mul_comm] using
            mul_le_mul hgd' hag (norm_nonneg _) (mul_nonneg hDg (Real.rpow_nonneg dist_nonneg _))))
      _ = _ := by ring
  calc
    _ = ‖(fderiv ℝ B x v-fderiv ℝ B y v)-
        (fderiv ℝ A x v (gradient g x)-fderiv ℝ A y v (gradient g y))‖ := by
      congr 1; dsimp only [A]; abel
    _ ≤ ‖fderiv ℝ B x v-fderiv ℝ B y v‖+
        ‖fderiv ℝ A x v (gradient g x)-fderiv ℝ A y v (gradient g y)‖ := norm_sub_le _ _
    _ ≤ DB*(dist x y)^α+(DA*(K:ℝ)+(LA:ℝ)*Dg)*(dist x y)^α := add_le_add hb' he
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradient.holder_C1 {R L α : ℝ} (hR : 0<R) {f : Plane → ℝ} {G : Plane → Plane}
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    (hf : ContinuousOn f (Metric.ball 0 R)) (hG : ContinuousOn G (Metric.ball 0 R))
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (G x) (G y)≤L*(dist x y)^α) :
    ContDiffOn ℝ 1 f (Metric.ball 0 (R/4)) ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ y∈Metric.ball (0 : Plane) (R/4),
        dist (fderiv ℝ f x) (fderiv ℝ f y)≤L*(dist x y)^α := by
  have hd : ∀ x∈Metric.ball (0 : Plane) (R/4),
      HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x :=
    fun x hx ↦ hw.continuous_hasFDerivAt hR hf hG hx
  have hsub : Metric.ball (0 : Plane) (R/4)⊆Metric.ball 0 R := Metric.ball_subset_ball (by linarith)
  constructor
  · rw [show (1 : WithTop ℕ∞)=0+1 by rfl,contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    refine ⟨fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    rw [contDiffOn_zero]
    apply ((InnerProductSpace.toDual ℝ Plane).continuous.comp_continuousOn (hG.mono hsub)).congr
    intro x hx
    exact (hd x hx).fderiv
  · intro x hx y hy
    rw [(hd x hx).fderiv,(hd y hy).fderiv,(InnerProductSpace.toDual ℝ Plane).isometry.dist_eq]
    exact hHolder x (hsub hx) y (hsub hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.directional_holder_C1 {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R α DA DB Dg D₀ : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) (hα : 0<α) (hα1 : α≤1)
    (hDA : 0≤DA) (hDB : 0≤DB) (hDg : 0≤Dg) (hD₀ : 0≤D₀)
    (hAHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D₀*(dist x y)^α)
    (hAd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ (fun z ↦ cmcJacobian (p z)) x) (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y)≤DA*(dist x y)^α)
    (hBd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ B x) (fderiv ℝ B y)≤DB*(dist x y)^α)
    (hgd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤Dg*(dist x y)^α)
    (v : Plane) (hv : ‖v‖≤1) :
    ∃ s L β : ℝ,0<s ∧ s≤R ∧ 0≤L ∧ 0<β ∧ β≤1 ∧
      ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ g y v) (Metric.ball 0 s) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (fderiv ℝ (fun z ↦ fderiv ℝ g z v) x) (fderiv ℝ (fun z ↦ fderiv ℝ g z v) y)≤L*(dist x y)^β := by
  obtain ⟨G,C,hGc,hGb,hC,hGe,henergy⟩ := hw.gradient_difference_data hg hp hpb hA hB hBb hR hgc
  obtain ⟨u,U,hue,hug,hlin⟩ := hw.scalar_derivative hg hp hpb hA hB hAc hBc hBb hR hgc v hv
  let S : Plane → Plane := fun y ↦ fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (G y)
  have hSc : Continuous S := ((hBc.continuous_fderiv (by simp)).clm_apply continuous_const).sub
    (((hAc.continuous_fderiv (by simp)).clm_apply continuous_const).clm_apply hGc)
  have hsub : Metric.ball (0 : Plane) (R/4)⊆Metric.ball 0 R := Metric.ball_subset_ball (by linarith)
  have hGe' (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) : G y=gradient g y := by
    apply hGe
    have hy' : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    linarith
  have hSH : ∀ x∈Metric.ball (0 : Plane) (R/4),∀ y∈Metric.ball (0 : Plane) (R/4),
      ‖S x-S y‖≤(DB+DA*(K:ℝ)+(LA:ℝ)*Dg)*(dist x y)^α := by
    intro x hx y hy
    dsimp only [S]
    rw [hGe' x hx,hGe' y hy]
    exact linear_cmc_source_holder hg hA hDA hDB hDg hAd hBd hgd hv (hsub hx) (hsub hy)
  have hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (R/4) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (U y)-S y))=0 := by
    intro ψ hψ hc hs
    rw [← hlin ψ hψ hc hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun y ↦ by
      dsimp only [S]
      by_cases hy : y∈Metric.ball (0 : Plane) (R/4)
      · rw [hGe' y hy]
      · rw [fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy (hs hy'))]; rfl
  obtain ⟨U',s,L,β,hs,hsR,hL,hβ,hβ1,hUc,hUe,hUh⟩ :=
    forced_cmc_linearized_holder_gradient hp hpb (by linarith : 0<R/4) hα hα1 hD₀
      (fun x hx y hy ↦ hAHolder x (hsub hx) y (hsub hy)) hSc
      (by positivity : 0≤DB+DA*(K:ℝ)+(LA:ℝ)*Dg) hSH u U hug hd
  have hsub' : Metric.ball (0 : Plane) s⊆Metric.ball 0 (R/4) := Metric.ball_subset_ball (by linarith)
  have hw' : PlaneWeakGradient (Metric.ball 0 s) (fun y ↦ fderiv ℝ g y v) U' :=
    (hug.mono hsub').local_congr measurableSet_ball
      (ae_restrict_of_ae_restrict_of_subset hsub' hue.symm) hUe
  have hfc : ContinuousOn (fun y ↦ fderiv ℝ g y v) (Metric.ball 0 s) :=
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const).mono (hsub'.trans hsub)
  exact ⟨s/4,L,β,by positivity,by linarith,hL,hβ,hβ1,hw'.holder_C1 hs hfc hUc hUh⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.mono {g : Plane → ℝ} {p B : Plane → Plane} {U W : Set Plane}
    (hw : LinearCMCEquation g p B U) (hW : W⊆U) : LinearCMCEquation g p B W :=
  fun ψ hψ hc hs ↦ hw ψ hψ hc (hs.trans hW)

lemma LinearCMCEquation.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane} {U : Set Plane}
    (hU : IsOpen U) (hw : LinearCMCEquation g p B U)
    (hg : EqOn g' g U) (hp : EqOn p' p U) (hB : EqOn B' B U) : LinearCMCEquation g' p' B' U := by
  intro ψ hψ hc hs
  rw [← hw ψ hψ hc hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ by
    dsimp only
    by_cases hy : y∈U
    · have he : g'=ᶠ[𝓝 y]g := by
        filter_upwards [hU.mem_nhds hy] with z hz
        exact hg hz
      have hG : gradient g' y=gradient g y := congrArg
        (fun L : Plane →L[ℝ] ℝ ↦ (InnerProductSpace.toDual ℝ Plane).symm L) he.fderiv_eq
      rw [hG,hp hy,hB hy]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hs h))]; rfl

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

def HolderNear {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (f : E → F) (x : E) : Prop :=
  ∃ r α C : ℝ,0<r ∧ 0<α ∧ α≤1 ∧ 0≤C ∧
    ∀ y∈Metric.ball x r,∀ z∈Metric.ball x r,dist (f y) (f z)≤C*(dist y z)^α

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.continuousAt [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : HolderNear f x) : ContinuousAt f x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have hd : Tendsto (fun y : E ↦ dist y x) (𝓝 x) (𝓝 0) := by
    simpa only [id_eq,dist_self] using ((continuous_id : Continuous (fun y : E ↦ y)).dist (continuous_const (y := x))).tendsto x
  have hlim : Tendsto (fun y : E ↦ C*(dist y x)^α) (𝓝 x) (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne',mul_zero] using (hd.rpow_const (Or.inr hα.le)).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hlim
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  exact hH y hy x (Metric.mem_ball_self hr)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.eventually [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : HolderNear f x) : ∀ᶠ y in 𝓝 x,HolderNear f y := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  filter_upwards [Metric.ball_mem_nhds x (by linarith : 0<r/2)] with y hy
  have hsub : Metric.ball y (r/2)⊆Metric.ball x r := by
    intro z hz
    have hz' := Metric.mem_ball.mp hz
    have hy' := Metric.mem_ball.mp hy
    have ht := dist_triangle z y x
    exact Metric.mem_ball.mpr (by linarith)
  exact ⟨r/2,α,C,by linarith,hα,hα1,hC,fun z hz w hw ↦ hH z (hsub hz) w (hsub hw)⟩

lemma HolderNear.contDiffAt_zero {f : E → F} {x : E} (hf : HolderNear f x) : ContDiffAt ℝ 0 f x := by
  obtain ⟨s,hS,hsc,hs⟩ := eventually_nhds_iff.mp hf.eventually
  exact _root_.contDiffAt_zero.mpr ⟨s,hsc.mem_nhds hs,fun y hy ↦ (hS y hy).continuousAt.continuousWithinAt⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.congr [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (hf : HolderNear f x) (he : f=ᶠ[𝓝 x]g) : HolderNear g x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,hs,hsE⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min r s,α,C,lt_min hr hs,hα,hα1,hC,?_⟩
  intro y hy z hz
  have hyR := (Metric.ball_subset_ball (min_le_left r s)) hy
  have hzR := (Metric.ball_subset_ball (min_le_left r s)) hz
  rw [← hsE ((Metric.ball_subset_ball (min_le_right r s)) hy),
    ← hsE ((Metric.ball_subset_ball (min_le_right r s)) hz)]
  exact hH y hyR z hzR

lemma ContDiffAt.holderNear {f : E → F} {x : E} (hf : ContDiffAt ℝ 1 f x) : HolderNear f x := by
  obtain ⟨C,S,hS,hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨r,1,C,hr,by norm_num,le_rfl,C.coe_nonneg,?_⟩
  intro y hy z hz
  simpa only [Real.rpow_one] using hLip.dist_le_mul y (hrS hy) z (hrS hz)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
lemma HolderNear.prodMk [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E}
    (hf : HolderNear f x) (hg : HolderNear g x) : HolderNear (fun y ↦ (f y,g y)) x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,β,D,hs,hβ,hβ1,hD,hJ⟩ := hg
  let ρ := min (min r s) (1/2)
  have hρ : 0<ρ := lt_min (lt_min hr hs) (by norm_num)
  have hρr : ρ≤r := (min_le_left _ _).trans (min_le_left _ _)
  have hρs : ρ≤ s := (min_le_left _ _).trans (min_le_right _ _)
  have hρα : ρ≤1/2 := min_le_right _ _
  refine ⟨ρ,min α β,C+D,hρ,lt_min hα hβ,(min_le_left _ _).trans hα1,add_nonneg hC hD,?_⟩
  intro y hy z hz
  have hd : dist y z≤1 := by
    have hy' := Metric.mem_ball.mp hy
    have hz' := Metric.mem_ball.mp hz
    have ht := dist_triangle_right y z x
    linarith
  have hhα : (dist y z)^α≤(dist y z)^(min α β) :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd (le_min hα.le hβ.le) (min_le_left _ _)
  have hhβ : (dist y z)^β≤(dist y z)^(min α β) :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd (le_min hα.le hβ.le) (min_le_right _ _)
  rw [Prod.dist_eq]
  apply max_le
  · exact ((hH y ((Metric.ball_subset_ball hρr) hy) z ((Metric.ball_subset_ball hρr) hz)).trans
      (mul_le_mul_of_nonneg_left hhα hC)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))
  · exact ((hJ y ((Metric.ball_subset_ball hρs) hy) z ((Metric.ball_subset_ball hρs) hz)).trans
      (mul_le_mul_of_nonneg_left hhβ hD)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))

lemma ContDiffAt.comp_holderNear {f : E → F} {g : F → G} {x : E}
    (hg : ContDiffAt ℝ 1 g (f x)) (hf : HolderNear f x) : HolderNear (g ∘ f) x := by
  obtain ⟨K,S,hS,hLip⟩ := hg.exists_lipschitzOnWith
  have hfcont := hf.continuousAt
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,hs,hsS⟩ := Metric.mem_nhds_iff.mp (hfcont hS)
  refine ⟨min r s,α,(K:ℝ)*C,lt_min hr hs,hα,hα1,mul_nonneg K.coe_nonneg hC,?_⟩
  intro y hy z hz
  calc
    _ ≤ (K:ℝ)*dist (f y) (f z) := hLip.dist_le_mul (f y)
      (hsS ((Metric.ball_subset_ball (min_le_right r s)) hy)) (f z)
      (hsS ((Metric.ball_subset_ball (min_le_right r s)) hz))
    _ ≤ (K:ℝ)*(C*(dist y z)^α) := mul_le_mul_of_nonneg_left
      (hH y ((Metric.ball_subset_ball (min_le_left r s)) hy)
        z ((Metric.ball_subset_ball (min_le_left r s)) hz)) K.coe_nonneg
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

def HolderJet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] : ℕ → (E → F) → E → Prop
  | 0,f,x => HolderNear f x
  | n+1,f,x => ContDiffAt ℝ 1 f x ∧ HolderJet n (fderiv ℝ f) x

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJet.congr {n : ℕ} {f g : E → F} {x : E} (hf : HolderJet n f x)
    (he : f=ᶠ[𝓝 x]g) : HolderJet n g x := by
  induction n generalizing F with
  | zero => exact hf.congr he
  | succ n ih =>
    exact ⟨hf.1.congr_of_eventuallyEq he.symm,ih hf.2 he.fderiv⟩

lemma HolderJet.holderNear {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) : HolderNear f x := by
  cases n with
  | zero => exact hf
  | succ n => exact ContDiffAt.holderNear hf.1

lemma HolderJet.pred {n : ℕ} {f : E → F} {x : E} (hf : HolderJet (n+1) f x) : HolderJet n f x := by
  induction n generalizing F with
  | zero => exact ContDiffAt.holderNear hf.1
  | succ n ih => exact ⟨hf.1,ih hf.2⟩

lemma HolderJet.of_le {n m : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) (hm : m≤n) : HolderJet m f x := by
  induction n with
  | zero => simpa only [Nat.le_zero.mp hm] using hf
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hm with he|he
    · simpa only [he] using hf
    · exact ih hf.pred (Nat.le_of_lt_succ he)

lemma HolderJet.contDiffAt {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) : ContDiffAt ℝ n f x := by
  induction n generalizing F with
  | zero => exact HolderNear.contDiffAt_zero hf
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fderiv ℝ f,?_,ih hf.2⟩
    have hdiff : ∀ᶠ y in 𝓝 x,DifferentiableAt ℝ f y :=
      (hf.1.eventually (by simp)).mono fun _ hy ↦ hy.differentiableAt_one
    exact ⟨{y|DifferentiableAt ℝ f y},hdiff,fun y hy ↦ hy.hasFDerivAt⟩

lemma ContDiffAt.holderJet {n : ℕ} {f : E → F} {x : E} (hf : ContDiffAt ℝ (n+1) f x) : HolderJet n f x := by
  induction n generalizing F with
  | zero => exact ContDiffAt.holderNear hf
  | succ n ih =>
    refine ⟨hf.of_le (by norm_cast; omega),?_⟩
    exact ih (hf.fderiv_right (by norm_cast))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJet.eventually {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) :
    ∀ᶠ y in 𝓝 x,HolderJet n f y := by
  induction n generalizing F with
  | zero => exact HolderNear.eventually hf
  | succ n ih => exact (hf.1.eventually (by simp)).and (ih hf.2)

lemma HolderJet.clm_comp {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x)
    (L : F →L[ℝ] G) : HolderJet n (L ∘ f) x := by
  induction n generalizing F G with
  | zero => exact ContDiffAt.comp_holderNear L.contDiff.contDiffAt hf
  | succ n ih =>
    refine ⟨L.contDiff.contDiffAt.comp x hf.1,?_⟩
    apply (ih hf.2 (ContinuousLinearMap.compL ℝ E F G L)).congr
    filter_upwards [hf.1.eventually (by simp)] with y hy
    exact ((L.hasFDerivAt).comp y hy.differentiableAt_one.hasFDerivAt).fderiv.symm

lemma HolderJet.prodMk {n : ℕ} {f : E → F} {g : E → G} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ (f y,g y)) x := by
  induction n generalizing F G with
  | zero => exact HolderNear.prodMk hf hg
  | succ n ih =>
    refine ⟨hf.1.prodMk hg.1,?_⟩
    have hh := (ih hf.2 hg.2).clm_comp
      (ContinuousLinearMap.prodₗᵢ ℝ (E := E) (F := F) (G := G)).toContinuousLinearEquiv.toContinuousLinearMap
    apply hh.congr
    filter_upwards [hf.1.eventually (by simp),hg.1.eventually (by simp)] with y hy hz
    exact (hy.differentiableAt_one.fderiv_prodMk hz.differentiableAt_one).symm

lemma HolderJet.smooth_comp {n : ℕ} {f : E → F} {g : F → G} {x : E}
    (hf : HolderJet n f x) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : HolderJet n (g ∘ f) x := by
  induction n generalizing E F G with
  | zero => exact ContDiffAt.comp_holderNear (hg.of_le (by simp)).contDiffAt hf
  | succ n ih =>
    refine ⟨(hg.of_le (by simp)).contDiffAt.comp x hf.1,?_⟩
    have hDg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hpair := (ih hf.pred hDg).prodMk hf.2
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (F →L[ℝ] G)×(E →L[ℝ] F) ↦ p.1.comp p.2) := contDiff_fst.clm_comp contDiff_snd
    apply (ih hpair hcomp).congr
    filter_upwards [hf.1.eventually (by simp)] with y hy
    exact (fderiv_comp y (hg.differentiable (by simp) (f y)) hy.differentiableAt_one).symm

lemma HolderJet.const {n : ℕ} {x : E} (c : F) : HolderJet n (fun _ : E ↦ c) x :=
  ContDiffAt.holderJet contDiffAt_const

lemma HolderJet.add {n : ℕ} {f g : E → F} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ f y+g y) x :=
  (hf.prodMk hg).smooth_comp (contDiff_fst.add contDiff_snd)

lemma HolderJet.sub {n : ℕ} {f g : E → F} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ f y-g y) x :=
  (hf.prodMk hg).smooth_comp (contDiff_fst.sub contDiff_snd)

lemma HolderJet.clm_apply {n : ℕ} {f : E → F →L[ℝ] G} {g : E → F} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ f y (g y)) x :=
  (hf.prodMk hg).smooth_comp (contDiff_fst.clm_apply contDiff_snd)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem WeakCMCGraph.directional_C1 {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R α C : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hα : 0<α) (hα1 : α≤1) (hC : 0≤C)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤C*(dist x y)^α)
    (v : Plane) (hv : ‖v‖≤1) :
    ∃ s : ℝ,0<s ∧ s≤R ∧ ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ g y v) (Metric.ball 0 s) := by
  obtain ⟨p,D,hp,hpb,hD,hpe,hpHolder⟩ := hw.holder_symbol_extension hg hK hR hgc hC hHolder
  obtain ⟨u,G,hue,hug,hlin⟩ := hw.scalar_linearized_equation hg hK hR hgc v hv
  have hsub : Metric.ball (0 : Plane) (R/4)⊆Metric.ball 0 (R/2) :=
    Metric.ball_subset_ball (by linarith)
  have hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (R/4) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0 := by
    intro ψ hψ hc hs
    rw [← hlin ψ hψ hc hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun y ↦ by
      dsimp only
      by_cases hy : y∈Metric.ball (0 : Plane) (R/4)
      · rw [hpe y (hsub hy)]
      · rw [fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy (hs hy'))]; rfl
  obtain ⟨G',s,L,β,hs,hsR,hL,hβ,hβ1,hGc,hGe,hGh⟩ :=
    cmc_linearized_holder_gradient hp hpb (by linarith : 0<R/4) hα hα1 hD
      (fun x hx y hy ↦ hpHolder x (hsub hx) y (hsub hy)) u G hug hd
  have hsR' : s≤R/4 := by linarith
  have hsub' : Metric.ball (0 : Plane) s⊆Metric.ball 0 (R/4) := Metric.ball_subset_ball hsR'
  have hsubR : Metric.ball (0 : Plane) s⊆Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hw' : PlaneWeakGradient (Metric.ball 0 s) (fun y ↦ fderiv ℝ g y v) G' :=
    ((hug.mono hsub').local_congr measurableSet_ball
      (ae_restrict_of_ae_restrict_of_subset hsub' hue.symm) hGe)
  have hfc : ContinuousOn (fun y ↦ fderiv ℝ g y v) (Metric.ball 0 s) :=
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const).mono hsubR
  have hder : ∀ x∈Metric.ball (0 : Plane) (s/4),
      HasFDerivAt (fun y ↦ fderiv ℝ g y v) ((InnerProductSpace.toDual ℝ Plane) (G' x)) x :=
    fun x hx ↦ hw'.continuous_hasFDerivAt hs hfc hGc hx
  refine ⟨s/4,by positivity,by linarith,?_⟩
  rw [show (1 : WithTop ℕ∞)=0+1 by rfl,contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
  refine ⟨fun x hx ↦ (hder x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  apply ((InnerProductSpace.toDual ℝ Plane).continuous.comp_continuousOn
    (hGc.mono (Metric.ball_subset_ball (by linarith : s/4≤ s)))).congr
  intro x hx
  exact (hder x hx).fderiv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_decompose (v : Plane) : v=v 0 • EuclideanSpace.single 0 (1 : ℝ)+
    v 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

theorem WeakCMCGraph.local_C2 {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R α C : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hα : 0<α) (hα1 : α≤1) (hC : 0≤C)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤C*(dist x y)^α) :
    ∃ s : ℝ,0<s ∧ s≤R ∧ ContDiffOn ℝ 2 g (Metric.ball 0 s) := by
  obtain ⟨s₀,hs₀,hs₀R,h₀⟩ := hw.directional_C1 hg hK hR hgc hα hα1 hC hHolder
    (EuclideanSpace.single 0 1) (by simp)
  obtain ⟨s₁,hs₁,hs₁R,h₁⟩ := hw.directional_C1 hg hK hR hgc hα hα1 hC hHolder
    (EuclideanSpace.single 1 1) (by simp)
  let s := min s₀ s₁
  have hs : 0<s := lt_min hs₀ hs₁
  have hsR : s≤R := (min_le_left _ _).trans hs₀R
  have h₀' := h₀.mono (Metric.ball_subset_ball (min_le_left s₀ s₁))
  have h₁' := h₁.mono (Metric.ball_subset_ball (min_le_right s₀ s₁))
  refine ⟨s,hs,hsR,?_⟩
  rw [show (2 : WithTop ℕ∞)=1+1 by norm_num,contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
  refine ⟨(hgc.differentiableOn (by norm_num)).mono (Metric.ball_subset_ball hsR),by simp,?_⟩
  apply contDiffOn_clm_apply.mpr
  intro v
  have he : (fun y ↦ fderiv ℝ g y v)=
      (fun y ↦ v 0*fderiv ℝ g y (EuclideanSpace.single 0 1)+
        v 1*fderiv ℝ g y (EuclideanSpace.single 1 1)) := by
    funext y
    conv_lhs => rw [plane_decompose v]
    simp
  rw [he]
  exact (contDiffOn_const.mul h₀').add (contDiffOn_const.mul h₁')

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HolderJet.plane_clm {n : ℕ} {A : E → Plane →L[ℝ] F} {x : E}
    (h₀ : HolderJet n (fun y ↦ A y (EuclideanSpace.single 0 1)) x)
    (h₁ : HolderJet n (fun y ↦ A y (EuclideanSpace.single 1 1)) x) : HolderJet n A x := by
  let e₀ : Plane →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ Plane) (EuclideanSpace.single 0 1)
  let e₁ : Plane →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ Plane) (EuclideanSpace.single 1 1)
  let T : F×F → Plane →L[ℝ] F := fun q ↦ e₀.smulRight q.1+e₁.smulRight q.2
  have hT : ContDiff ℝ (⊤ : ℕ∞) T :=
    (contDiff_const.smulRight contDiff_fst).add (contDiff_const.smulRight contDiff_snd)
  apply ((h₀.prodMk h₁).smooth_comp hT).congr
  exact Eventually.of_forall fun y ↦ by
    apply ContinuousLinearMap.ext
    intro v
    change e₀ v • A y (EuclideanSpace.single 0 1)+e₁ v • A y (EuclideanSpace.single 1 1)=A y v
    have he₀ : e₀ v=v 0 := by simp [e₀,EuclideanSpace.inner_single_left]
    have he₁ : e₁ v=v 1 := by simp [e₁,EuclideanSpace.inner_single_left]
    rw [he₀,he₁]
    conv_rhs => rw [plane_decompose v]
    simp

lemma HolderJet.directional {n : ℕ} {f : Plane → ℝ} {x : Plane}
    (hf : HolderJet (n+1) f x) (v : Plane) : HolderJet n (fun y ↦ fderiv ℝ f y v) x :=
  hf.2.clm_apply (HolderJet.const v)

lemma HolderJet.of_directionals {n : ℕ} {f : Plane → ℝ} {x : Plane}
    (hf : ContDiffAt ℝ 1 f x)
    (h₀ : HolderJet n (fun y ↦ fderiv ℝ f y (EuclideanSpace.single 0 1)) x)
    (h₁ : HolderJet n (fun y ↦ fderiv ℝ f y (EuclideanSpace.single 1 1)) x) : HolderJet (n+1) f x :=
  ⟨hf,HolderJet.plane_clm h₀ h₁⟩

lemma HolderJet.gradient {n : ℕ} {f : Plane → ℝ} {x : Plane}
    (hf : HolderJet (n+1) f x) : HolderJet n (gradient f) x :=
  hf.2.clm_comp (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.toContinuousLinearMap

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus
variable {E F G H I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup I] [NormedSpace ℝ I]

end CubicTorus
end
end
end

end OAI
