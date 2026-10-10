import Mathlib
import OAI.Geometry.CubicTorus.Curvature.CmcStretch

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma smooth_directional_commute {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w x : Plane) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w =
      fderiv ℝ (fun y ↦ fderiv ℝ f y w) x v := by
  rw [fderiv_fderiv_apply hf,fderiv_fderiv_apply hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)) w v

lemma smooth_laplacian {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (Δ f) := by
  have he := funext (laplacian_eq_sum_directional hf)
  rw [he]
  apply ContDiff.sum
  intro i _
  exact (((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).fderiv_right (m := (⊤ : ℕ∞))
    (by simp)).clm_apply contDiff_const

lemma laplacian_directional {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v x : Plane) : Δ (fun y ↦ fderiv ℝ f y v) x = fderiv ℝ (Δ f) x v := by
  have hd (w : Plane) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ f y w) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hdd (w : Plane) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z w) y w) :=
    ((hd w).fderiv_right (by simp)).clm_apply contDiff_const
  rw [laplacian_eq_sum_directional (hd v),funext (laplacian_eq_sum_directional hf),
    fderiv_fun_sum (fun w _ ↦ (hdd _).differentiable (by simp) |>.differentiableAt)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z v) y ((stdOrthonormalBasis ℝ Plane) i))=
    (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z ((stdOrthonormalBasis ℝ Plane) i)) y v) from
    funext (fun y ↦ smooth_directional_commute hf _ _ y)]
  exact smooth_directional_commute (hd _) _ _ _

lemma PlaneWeakGradient.harmonic_component {S : Set Plane}
    {u : Plane → ℝ} {G : Plane → Plane} (hg : PlaneWeakGradient S u G)
    (hh : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,u y*Δ ψ y)=0)
    (v : Plane) {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S) :
    (∫ y,⟪G y,v⟫*Δ ψ y)=0 := by
  have hlc : HasCompactSupport (Δ ψ) := hc.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset hψ)
  rw [hg v (Δ ψ) (smooth_laplacian hψ) hlc ((laplacian_tsupport_subset hψ).trans hs)]
  simp_rw [← laplacian_directional hψ]
  rw [hh _ ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hs),neg_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] [μ.IsAddHaarMeasure] in
lemma scalar_convolution_norm_le [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [BorelSpace X] [μ.IsAddHaarMeasure] {f k : X → ℝ} (hf : Integrable f μ)
    {C : ℝ} (hb : ∀ x,‖k x‖≤C) (x : X) :
    ‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x‖≤C*(∫ y,‖f y‖ ∂μ) := by
  rw [convolution_mul]
  calc
    _ ≤ ∫ y,C*‖f y‖ ∂μ := norm_integral_le_of_norm_le (hf.norm.const_mul C)
      (Eventually.of_forall fun y ↦ by
        rw [norm_mul,mul_comm C]
        exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

lemma first_deriv_convolution_le {f k : X → ℝ} (hf : Integrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x,‖fderiv ℝ k x‖≤C) (x : X) :
    ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x‖≤C*(∫ y,‖f y‖ ∂μ) := by
  have hm : 0≤∫ y,‖f y‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hm)
  intro v
  rw [fderiv_compact_convolution hf.locallyIntegrable hk hs]
  have he := scalar_convolution_norm_le hf (fun y ↦
    (ContinuousLinearMap.le_opNorm (fderiv ℝ k y) v).trans
      (mul_le_mul_of_nonneg_right (hb y) (norm_nonneg v))) x
  convert he using 1
  ring

lemma compact_convolution_value_lipschitz {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) :
    ∃ C : ℝ,0<C ∧ ∀ f : X → ℝ,Integrable f μ →
      (∀ x,‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x‖≤C*(∫ y,‖f y‖ ∂μ)) ∧
      (∀ x y,‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x-
        (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y‖≤C*(∫ z,‖f z‖ ∂μ)*‖x-y‖) := by
  obtain ⟨C₀,hC₀,hb₀⟩ := continuous_compact_norm_bound hk.continuous hs
  obtain ⟨C₁,hC₁,hb₁⟩ := continuous_compact_norm_bound
    (hk.continuous_fderiv (by simp)) (hs.fderiv ℝ)
  refine ⟨max C₀ C₁,lt_of_lt_of_le hC₀ (le_max_left _ _),fun f hf ↦ ⟨?_,?_⟩⟩
  · exact scalar_convolution_norm_le hf (fun x ↦ (hb₀ x).trans (le_max_left _ _))
  · intro x y
    have hu := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hk
    exact (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hu.differentiable (by simp) |>.differentiableAt)
      (fun z _ ↦ first_deriv_convolution_le hf hk hs
        (hC₀.le.trans (le_max_left _ _)) (fun t ↦ (hb₁ t).trans (le_max_right _ _)) z)
      (mem_univ y) (mem_univ x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

theorem plane_weak_harmonic_value_lipschitz {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ,0<C ∧ ∀ f : Plane → ℝ,Integrable f →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,f y*Δ ψ y)=0) →
      ∃ u : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) u ∧
        f=ᵐ[volume.restrict (Metric.ball 0 R)] u ∧
        (∀ x,‖u x‖≤C*(∫ z,‖f z‖)) ∧
        (∀ x y,‖u x-u y‖≤C*(∫ z,‖f z‖)*‖x-y‖) := by
  let L := Complex.orthonormalBasisOneI.repr
  obtain ⟨k,κ,hk,hks,hrad,hc,hκ,_,hi⟩ := exists_radial_smoothing_kernel hR
  obtain ⟨C,hC,hbound⟩ := compact_convolution_value_lipschitz (μ := volume) hk hks
  refine ⟨C,hC,fun f hf hw ↦ ?_⟩
  let v := (f ∘ L) ⋆[ContinuousLinearMap.mul ℝ ℝ] k
  have hfL : Integrable (f ∘ L) := (L.measurePreserving.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hks.contDiff_convolution_right _ hfL.locallyIntegrable hk
  have heI : (∫ z,‖(f ∘ L) z‖)=∫ z,‖f z‖ :=
    by
      dsimp only [Function.comp_def]
      rw [L.measurePreserving.integral_comp L.toMeasurableEquiv.measurableEmbedding (fun z ↦ ‖f z‖)]
  obtain ⟨hb,hl⟩ := hbound _ hfL
  rw [heI] at hb hl
  refine ⟨v ∘ L.symm,hv.comp L.symm.contDiff,?_,?_,?_⟩
  · have he := weak_harmonic_radial_reproduction hR (Subset.refl _) hfL.locallyIntegrable
      (weak_harmonic_comp_isometry L hw) hk hks hrad hc hκ hi
    have hmp : MeasurePreserving L.symm
        (volume.restrict (Metric.ball (0 : Plane) R))
        (volume.restrict (Metric.ball (0 : ℂ) R)) := by
      simpa only [L.symm.preimage_ball,map_zero] using
        L.symm.measurePreserving.restrict_preimage (measurableSet_ball (x := (0 : ℂ)) (ε := R))
    have hh := hmp.quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [hh] with z hz
    change f (L (L.symm z))=v (L.symm z) at hz
    simpa only [LinearIsometryEquiv.apply_symm_apply,Function.comp_apply] using hz
  · intro x
    simpa only [v,Function.comp_apply] using hb (L.symm x)
  · intro x y
    have hh := hl (L.symm x) (L.symm y)
    simpa only [v,Function.comp_apply,← map_sub,L.symm.norm_map] using hh

theorem plane_L2_harmonic_value_lipschitz {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ,0<C ∧ ∀ f : Plane → ℝ,MemLp f 2 volume →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,f y*Δ ψ y)=0) →
      ∃ u : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) u ∧
        f=ᵐ[volume.restrict (Metric.ball 0 R)] u ∧
        (∀ x,‖u x‖≤C*(∫ z in Metric.closedBall 0 (4*R),‖f z‖)) ∧
        (∀ x y,‖u x-u y‖≤C*(∫ z in Metric.closedBall 0 (4*R),‖f z‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := plane_weak_harmonic_value_lipschitz hR
  refine ⟨C,hC,fun f hf hw ↦ ?_⟩
  let S := Metric.closedBall (0 : Plane) (4*R)
  let F := S.indicator f
  have hfi : IntegrableOn f S := (hf.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall _ _)
  have hF : Integrable F := hfi.integrable_indicator measurableSet_closedBall
  have hFw : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,F y*Δ ψ y)=0 := by
    intro ψ hψ hc hs
    rw [← hw ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈S
    · simp only [F,indicator_of_mem hy]
    · have hz : Δ ψ y=0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hy (Metric.ball_subset_closedBall (hs (laplacian_tsupport_subset hψ h))))
      simp only [hz,mul_zero]
  obtain ⟨u,hu,he,hb,hl⟩ := hbound F hF hFw
  have heI : (∫ z,‖F z‖)=∫ z in S,‖f z‖ := by
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards [] with z
    change ‖S.indicator f z‖=S.indicator (fun z ↦ ‖f z‖) z
    by_cases hz : z∈S <;> simp [hz]
  refine ⟨u,hu,?_,by simpa only [heI] using hb,by simpa only [heI] using hl⟩
  filter_upwards [he,ae_restrict_mem measurableSet_ball] with y hy hys
  have hS : y∈S := Metric.ball_subset_closedBall
    ((Metric.ball_subset_ball (by linarith : R≤4*R)) hys)
  simpa only [F,indicator_of_mem hS] using hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

theorem plane_harmonic_gradient_bound {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ,0<C ∧
      ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
      PlaneWeakGradient (Metric.ball 0 (4*R)) u G →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,fderiv ℝ ψ y (G y))=0) →
      ∃ H : Plane → Plane,ContDiff ℝ (⊤ : ℕ∞) H ∧
        (G : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 R)] H ∧
        (∀ x,‖H x‖≤C*(∫ z in Metric.closedBall 0 (4*R),‖G z‖)) ∧
        (∀ x y,‖H x-H y‖≤C*(∫ z in Metric.closedBall 0 (4*R),‖G z‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := plane_L2_harmonic_value_lipschitz hR
  refine ⟨2*C,by positivity,fun u G hg hd ↦ ?_⟩
  let b := stdOrthonormalBasis ℝ Plane
  let S := Metric.closedBall (0 : Plane) (4*R)
  let M := ∫ z in S,‖G z‖
  have hmem (i : Fin (Module.finrank ℝ Plane)) : MemLp (fun y ↦ ⟪G y,b i⟫) 2 volume := by
    simpa [Function.comp_def,real_inner_comm] using (innerSL ℝ (b i)).comp_memLp' (Lp.memLp G)
  have hh (i : Fin (Module.finrank ℝ Plane)) := hbound _ (hmem i)
    (fun ψ hψ hc hs ↦ hg.harmonic_component (fun φ hφ hfc hfs ↦ hg.weak_laplacian hd hφ hfc hfs)
      (b i) hψ hc hs)
  choose H hH he hb hl using hh
  have hGi : IntegrableOn (fun z ↦ ‖G z‖) S :=
    ((Lp.memLp G).norm.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _)
  have hM (i : Fin (Module.finrank ℝ Plane)) : (∫ z in S,‖⟪G z,b i⟫‖)≤M := by
    apply integral_mono
      (((hmem i).norm.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _)) hGi
    intro z
    simpa only [b.orthonormal.norm_eq_one i,mul_one] using norm_inner_le_norm (G z) (b i)
  let F : Plane → Plane := fun y ↦ ∑ i,H i y • b i
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := ContDiff.sum fun i _ ↦ (hH i).smul contDiff_const
  refine ⟨F,hF,?_,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr he] with y hy
    change G y=∑ i,H i y • b i
    rw [← b.sum_repr' (G y)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hy i,real_inner_comm]
  · intro x
    change ‖∑ i,H i x • b i‖≤_
    calc
      _ ≤ ∑ i,‖H i x • b i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin (Module.finrank ℝ Plane),C*M := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [norm_smul,b.orthonormal.norm_eq_one i,mul_one] using
          (hb i x).trans (mul_le_mul_of_nonneg_left (hM i) hC.le)
      _ = _ := by simp [Plane,finrank_euclideanSpace]; ring
  · intro x y
    change ‖(∑ i,H i x • b i)-(∑ i,H i y • b i)‖≤_
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i,‖H i x • b i-H i y • b i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin (Module.finrank ℝ Plane),C*M*‖x-y‖ := by
        apply Finset.sum_le_sum
        intro i _
        simp only [← sub_smul,norm_smul,b.orthonormal.norm_eq_one i,mul_one]
        exact (hl i x y).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM i) hC.le) (norm_nonneg _))
      _ = _ := by simp [Plane,finrank_euclideanSpace]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeChange_real (L : Plane ≃L[ℝ] Plane) {S : Set Plane} (hS : MeasurableSet S) :
    (volume : Measure Plane).real (L ⁻¹' S)=
      (planeChangeFactor L : ℝ)*(volume : Measure Plane).real S := by
  simp only [Measure.real]
  rw [← Measure.map_apply L.continuous.measurable hS,planeChange_map,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.coe_toReal]

lemma planeChangeFactor_le_four (L : Plane ≃L[ℝ] Plane)
    (hL : ∀ y,‖L.symm y‖≤2*‖y‖) : (planeChangeFactor L : ℝ)≤4 := by
  have hs : L ⁻¹' Metric.ball (0 : Plane) 1⊆Metric.ball 0 2 := by
    intro y hy
    have hy' : ‖L y‖<1 := by simpa only [mem_preimage,Metric.mem_ball,dist_zero_right] using hy
    have hn := hL (L y)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hn
    simpa only [Metric.mem_ball,dist_zero_right] using hn.trans_lt (by linarith : 2*‖L y‖<2)
  have hv : (volume : Measure Plane) (Metric.ball (0 : Plane) 2)≠⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hh := ENNReal.toReal_mono hv (measure_mono hs)
  change (volume : Measure Plane).real (L ⁻¹' Metric.ball 0 1)≤volume.real (Metric.ball 0 2) at hh
  rw [planeChange_real L measurableSet_ball,plane_ball_real (by norm_num : (0:ℝ)≤1),
    plane_ball_real (by norm_num : (0:ℝ)≤2)] at hh
  nlinarith [Real.pi_pos]

lemma planeChange_setIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Plane ≃L[ℝ] Plane) {S : Set Plane} (hS : MeasurableSet S) (f : Plane → X) :
    (∫ y in L ⁻¹' S,f (L y))=(planeChangeFactor L : ℝ) • ∫ y in S,f y := by
  rw [← integral_indicator (hS.preimage L.continuous.measurable),← integral_indicator hS,
    ← planeChange_integral L]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : L y∈S <;> simp [hy]

lemma planeChange_closedBall_L1 (L : Plane ≃L[ℝ] Plane)
    (hL : ∀ y,‖L y‖≤2*‖y‖) (hLi : ∀ y,‖L.symm y‖≤2*‖y‖)
    (G : Lp Plane 2 (volume : Measure Plane)) {R : ℝ} (hR : 0≤R) :
    (∫ y in Metric.closedBall 0 (4*R),‖L (G (L y))‖)≤
      8*(∫ y in Metric.closedBall 0 (8*R),‖G y‖) := by
  let S := Metric.closedBall (0 : Plane) (8*R)
  let T := Metric.closedBall (0 : Plane) (4*R)
  have hs : T⊆L ⁻¹' S := by
    intro y hy
    have hy' : ‖y‖≤4*R := by simpa only [T,Metric.mem_closedBall,dist_zero_right] using hy
    change ‖L y-0‖≤8*R
    rw [sub_zero]
    calc
      ‖L y‖ ≤ 2*‖y‖ := hL y
      _ ≤ 2*(4*R) := by
        simpa only [mul_comm] using mul_le_mul hy' (le_refl (2 : ℝ))
          (by norm_num) (mul_nonneg (by norm_num) hR)
      _ = 8*R := by ring
  have hi := planeChange_memLp L (Lp.memLp G)
  have hj := L.toContinuousLinearMap.comp_memLp' hi
  have hcompact : IsCompact (L ⁻¹' S) := L.toHomeomorph.isCompact_preimage.mpr
    (isCompact_closedBall (0 : Plane) (8*R))
  have hInt : IntegrableOn (fun y ↦ ‖G (L y)‖) (L ⁻¹' S) :=
    (hi.norm.locallyIntegrable (by norm_num)).integrableOn_isCompact hcompact
  have hIntT : IntegrableOn (fun y ↦ ‖L (G (L y))‖) T :=
    (hj.norm.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _)
  have hM : 0≤∫ y in S,‖G y‖ := integral_nonneg fun _ ↦ norm_nonneg _
  calc
    _ ≤ ∫ y in T,2*‖G (L y)‖ := integral_mono hIntT ((hInt.mono_set hs).const_mul 2)
      (fun y ↦ hL (G (L y)))
    _ = 2*(∫ y in T,‖G (L y)‖) := integral_const_mul _ _
    _ ≤ 2*(∫ y in L ⁻¹' S,‖G (L y)‖) := by
      exact mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hInt (Eventually.of_forall fun _ ↦ norm_nonneg _) hs.eventuallyLE) (by norm_num)
    _ = 2*(planeChangeFactor L : ℝ)*(∫ y in S,‖G y‖) := by
      rw [planeChange_setIntegral L (S := S) measurableSet_closedBall (fun y ↦ ‖G y‖)]
      simp only [smul_eq_mul]; ring
    _ ≤ _ := by nlinarith [planeChangeFactor_le_four L hLi]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem frozen_cmc_gradient_bound {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ,0<C ∧ ∀ p : Plane,‖p‖≤1 →
      ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
      PlaneWeakGradient (Metric.ball 0 (8*R)) u G →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G y)))=0) →
      ∃ H : Plane → Plane,ContDiff ℝ (⊤ : ℕ∞) H ∧
        (G : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] H ∧
        (∀ x,‖H x‖≤C*(∫ z in Metric.closedBall 0 (8*R),‖G z‖)) ∧
        (∀ x y,‖H x-H y‖≤C*(∫ z in Metric.closedBall 0 (8*R),‖G z‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := plane_harmonic_gradient_bound hR
  refine ⟨32*C,by positivity,fun p hp u G hg hd ↦ ?_⟩
  let L := cmcMetricEquiv p
  have hu := planeChange_memLp L (Lp.memLp u)
  have hG := L.toContinuousLinearMap.comp_memLp' (planeChange_memLp L (Lp.memLp G))
  let u' := hu.toLp ((u : Plane → ℝ) ∘ L)
  let G' := hG.toLp (fun y ↦ L (G (L y)))
  have hraw := hg.comp_selfAdjoint L (cmcCompress_symm p)
  have hg' : PlaneWeakGradient (Metric.ball 0 (4*R)) u' G' :=
    (hraw.congr hu.coeFn_toLp hG.coeFn_toLp).mono (cmcMetricEquiv_ball hp R)
  have hd' : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,fderiv ℝ ψ y (G' y))=0 := by
    intro ψ hψ hc hs
    have hh := frozen_cmc_divergence_change p (G : Plane → Plane) hd ψ hψ hc
      (hs.trans (cmcMetricEquiv_ball hp R))
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with y hy
    exact congrArg (fderiv ℝ ψ y) hy
  obtain ⟨H,hH,he,hb,hl⟩ := hbound u' G' hg' hd'
  let M := ∫ z in Metric.closedBall (0 : Plane) (8*R),‖G z‖
  have hM : (∫ z in Metric.closedBall 0 (4*R),‖G' z‖)≤8*M := by
    have hh := planeChange_closedBall_L1 L (cmcMetricEquiv_norm hp)
      (cmcMetricEquiv_symm_norm hp) G hR.le
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hG.coeFn_toLp] with z hz
    exact congrArg norm hz
  let F : Plane → Plane := L.symm ∘ H ∘ L.symm
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := L.symm.contDiff.comp (hH.comp L.symm.contDiff)
  refine ⟨F,hF,?_,?_,?_⟩
  · have he' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) R → G' y=H y :=
      (ae_restrict_iff' measurableSet_ball).mp he
    have he'' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) R → G (L y)=L.symm (H y) := by
      filter_upwards [he',hG.coeFn_toLp] with y hy hz hys
      have hx : L (G (L y))=H y := hz.symm.trans (hy hys)
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg L.symm hx
    have he''' := planeChange_ae_prop L.symm he''
    change ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Plane) (R/2)), G y=F y
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [he'''] with y hy hys
    have hn : ‖y‖<R/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hys
    have hLy : L.symm y∈Metric.ball (0 : Plane) R := by
      rw [Metric.mem_ball,dist_zero_right]
      exact (cmcMetricEquiv_symm_norm hp y).trans_lt (by linarith)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,F,Function.comp_apply] using hy hLy
  · intro x
    have hb' := (hb (L.symm x)).trans (mul_le_mul_of_nonneg_left hM hC.le)
    have hMn : 0≤M := integral_nonneg fun _ ↦ norm_nonneg _
    change ‖L.symm (H (L.symm x))‖≤_
    exact (cmcMetricEquiv_symm_norm hp _).trans (by nlinarith)
  · intro x y
    change ‖L.symm (H (L.symm x))-L.symm (H (L.symm y))‖≤_
    rw [← map_sub]
    calc
      _ ≤ 2*‖H (L.symm x)-H (L.symm y)‖ := cmcMetricEquiv_symm_norm hp _
      _ ≤ 2*(C*(∫ z in Metric.closedBall 0 (4*R),‖G' z‖)*‖L.symm x-L.symm y‖) :=
        mul_le_mul_of_nonneg_left (hl _ _) (by norm_num)
      _ ≤ 2*(C*(8*M)*(2*‖x-y‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hM hC.le
        · rw [← map_sub]; exact cmcMetricEquiv_symm_norm hp _
        · exact norm_nonneg _
        · exact mul_nonneg hC.le (mul_nonneg (by norm_num) (integral_nonneg fun _ ↦ norm_nonneg _))
      _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeScaleEquiv (r : ℝ) (hr : r≠0) : Plane ≃L[ℝ] Plane :=
  (LinearEquiv.smulOfNeZero ℝ Plane r hr).toContinuousLinearEquiv

lemma planeScaleEquiv_apply (r : ℝ) (hr : r≠0) (y : Plane) :
    planeScaleEquiv r hr y=r • y := rfl

lemma planeScaleEquiv_symm_apply (r : ℝ) (hr : r≠0) (y : Plane) :
    (planeScaleEquiv r hr).symm y=r⁻¹ • y := rfl

lemma planeScaleEquiv_preimage_ball {r : ℝ} (hr : 0<r) (s : ℝ) :
    planeScaleEquiv r hr.ne' ⁻¹' Metric.ball (0 : Plane) (r*s)=Metric.ball 0 s := by
  ext y
  simp only [mem_preimage,Metric.mem_ball,dist_zero_right,planeScaleEquiv_apply,
    norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  exact mul_lt_mul_iff_right₀ hr

lemma planeScaleEquiv_preimage_closedBall {r : ℝ} (hr : 0<r) (s : ℝ) :
    planeScaleEquiv r hr.ne' ⁻¹' Metric.closedBall (0 : Plane) (r*s)=Metric.closedBall 0 s := by
  ext y
  simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right,planeScaleEquiv_apply,
    norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  exact mul_le_mul_iff_right₀ hr

lemma planeScaleFactor {r : ℝ} (hr : 0<r) :
    (planeChangeFactor (planeScaleEquiv r hr.ne') : ℝ)=r⁻¹^2 := by
  have hh := planeChange_real (planeScaleEquiv r hr.ne')
    (S := Metric.ball (0 : Plane) (r*1)) measurableSet_ball
  rw [planeScaleEquiv_preimage_ball hr,plane_ball_real (by norm_num : (0:ℝ)≤1),
    plane_ball_real (by positivity : 0≤r*1)] at hh
  simp only [mul_one,one_pow] at hh
  field_simp
  nlinarith [Real.pi_pos]

lemma planeScale_setIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {r : ℝ} (hr : 0<r) (s : ℝ) (f : Plane → X) :
    (∫ y in Metric.closedBall 0 s,f (r • y))=
      (r⁻¹^2) • ∫ y in Metric.closedBall 0 (r*s),f y := by
  have hh := planeChange_setIntegral (planeScaleEquiv r hr.ne')
    (S := Metric.closedBall (0 : Plane) (r*s)) measurableSet_closedBall f
  simpa only [planeScaleEquiv_preimage_closedBall hr,planeScaleEquiv_apply,planeScaleFactor hr] using hh

lemma constant_divergence_scale {S : Set Plane} {r : ℝ} (hr : 0<r)
    (A : Plane →L[ℝ] Plane) (G : Plane → Plane)
    (hdiv : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (A (G y)))=0) :
    ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆planeScaleEquiv r hr.ne' ⁻¹' S →
      (∫ y,fderiv ℝ ψ y (r • A (G (r • y))))=0 := by
  let L := planeScaleEquiv r hr.ne'
  intro ψ hψ hc hs
  let φ : Plane → ℝ := ψ ∘ L.symm
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp L.symm.contDiff
  have hφc : HasCompactSupport φ := hc.comp_homeomorph L.symm.toHomeomorph
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ L.symm.toHomeomorph)⊆S
    rw [tsupport_comp_eq_preimage ψ L.symm.toHomeomorph]
    intro z hz
    have hh : L (L.symm z)∈S := hs hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (z : Plane) : fderiv ℝ φ z (A (G z))=
      r⁻¹*fderiv ℝ ψ (L.symm z) (A (G z)) := by
    rw [fderiv_comp z (hψ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.coe_comp,Function.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    change fderiv ℝ ψ (L.symm z) (r⁻¹ • A (G z))=_
    rw [map_smul,smul_eq_mul]
  have hh := hdiv φ hφ hφc hφs
  simp_rw [hd] at hh
  rw [integral_const_mul] at hh
  have hh0 : (∫ z,fderiv ℝ ψ (L.symm z) (A (G z)))=0 :=
    (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hr.ne')
  have he := planeChange_integral L (fun z ↦ fderiv ℝ ψ (L.symm z) (A (G z)))
  simp only [ContinuousLinearEquiv.symm_apply_apply,hh0,smul_zero] at he
  simp only [map_smul,smul_eq_mul,integral_const_mul]
  change r*(∫ y,fderiv ℝ ψ y (A (G (L y))))=0
  rw [he,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem frozen_cmc_gradient_scaled :
    ∃ C : ℝ,0<C ∧ ∀ r : ℝ,0<r → ∀ p : Plane,‖p‖≤1 →
      ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
      PlaneWeakGradient (Metric.ball 0 (8*r)) u G →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (8*r) → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G y)))=0) →
      ∃ H : Plane → Plane,ContDiff ℝ (⊤ : ℕ∞) H ∧
        (G : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (r/2))] H ∧
        (∀ x,‖H x‖≤C*r⁻¹^2*(∫ z in Metric.closedBall 0 (8*r),‖G z‖)) ∧
        (∀ x y,‖H x-H y‖≤C*r⁻¹^3*(∫ z in Metric.closedBall 0 (8*r),‖G z‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := frozen_cmc_gradient_bound (by norm_num : (0:ℝ)<1)
  refine ⟨C,hC,fun r hr p hp u G hg hd ↦ ?_⟩
  let L := planeScaleEquiv r hr.ne'
  have hu := planeChange_memLp L (Lp.memLp u)
  have hG := L.toContinuousLinearMap.comp_memLp' (planeChange_memLp L (Lp.memLp G))
  let u' := hu.toLp ((u : Plane → ℝ) ∘ L)
  let G' := hG.toLp (fun y ↦ L (G (L y)))
  have hpre : L ⁻¹' Metric.ball (0 : Plane) (8*r)=Metric.ball 0 (8*1) := by
    simpa only [mul_comm r,mul_one] using planeScaleEquiv_preimage_ball hr 8
  have hg' : PlaneWeakGradient (Metric.ball 0 (8*1)) u' G' := by
    rw [← hpre]
    apply (hg.comp_selfAdjoint L ?_).congr hu.coeFn_toLp hG.coeFn_toLp
    intro a b
    change ⟪r • a,b⟫=⟪a,r • b⟫
    simp only [real_inner_smul_left,real_inner_smul_right]
  have hd' : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*1) → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G' y)))=0 := by
    intro ψ hψ hc hs
    have hh := constant_divergence_scale hr (cmcJacobian p) (G : Plane → Plane) hd
      ψ hψ hc (by change tsupport ψ⊆L ⁻¹' Metric.ball 0 (8*r); rw [hpre]; exact hs)
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with y hy
    change G' y=r • G (r • y) at hy
    rw [hy]
    rw [map_smul]
  obtain ⟨H,hH,he,hb,hl⟩ := hbound p hp u' G' hg' hd'
  let M := ∫ z in Metric.closedBall (0 : Plane) (8*r),‖G z‖
  have hM : (∫ z in Metric.closedBall 0 (8*1),‖G' z‖)=r⁻¹*M := by
    have heq : (∫ z in Metric.closedBall 0 (8*1),‖G' z‖)=
        ∫ z in Metric.closedBall 0 8,‖r • G (r • z)‖ := by
      norm_num
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hG.coeFn_toLp] with z hz
      exact congrArg norm hz
    rw [heq]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hr,integral_const_mul]
    rw [planeScale_setIntegral hr 8 (fun z ↦ ‖G z‖)]
    simp only [smul_eq_mul,mul_comm r 8]
    change r*(r⁻¹^2*M)=r⁻¹*M
    field_simp
  have hb' : ∀ x,‖H x‖≤C*(r⁻¹*M) := by
    simpa only [hM] using hb
  have hl' : ∀ x y,‖H x-H y‖≤(C*(r⁻¹*M))*‖x-y‖ := by
    simpa only [hM] using hl
  let F : Plane → Plane := L.symm ∘ H ∘ L.symm
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := L.symm.contDiff.comp (hH.comp L.symm.contDiff)
  refine ⟨F,hF,?_,?_,?_⟩
  · have he' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) (1/2) → G' y=H y :=
      (ae_restrict_iff' measurableSet_ball).mp he
    have he'' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) (1/2) → G (L y)=L.symm (H y) := by
      filter_upwards [he',hG.coeFn_toLp] with y hy hz hys
      have hx : L (G (L y))=H y := hz.symm.trans (hy hys)
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg L.symm hx
    have he''' := planeChange_ae_prop L.symm he''
    change ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Plane) (r/2)),G y=F y
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [he'''] with y hy hys
    have hLy : L.symm y∈Metric.ball (0 : Plane) (1/2) := by
      have hn : ‖y‖<r/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hys
      change ‖r⁻¹ • y-0‖<1/2
      rw [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      apply (mul_lt_mul_of_pos_left hn (inv_pos.mpr hr)).trans_le
      field_simp
      norm_num
    simpa only [ContinuousLinearEquiv.apply_symm_apply,F,Function.comp_apply] using hy hLy
  · intro x
    change ‖r⁻¹ • H (L.symm x)‖≤_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ r⁻¹*(C*(r⁻¹*M)) := mul_le_mul_of_nonneg_left (hb' _) (inv_pos.mpr hr).le
      _ = _ := by ring
  · intro x y
    change ‖r⁻¹ • H (L.symm x)-r⁻¹ • H (L.symm y)‖≤_
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ r⁻¹*((C*(r⁻¹*M))*‖L.symm x-L.symm y‖) :=
        mul_le_mul_of_nonneg_left (hl' _ _) (inv_pos.mpr hr).le
      _ = _ := by
        change r⁻¹*((C*(r⁻¹*M))*‖r⁻¹ • x-r⁻¹ • y‖)=_
        rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
        ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_vector_norm_sq_integrable (G : Lp Plane 2 (volume : Measure Plane)) :
    Integrable (fun y ↦ ‖G y‖^2) := by
  exact (memLp_two_iff_integrable_sq (Lp.memLp G).norm.aestronglyMeasurable).mp
    (Lp.memLp G).norm

lemma plane_closedBall_mass_le {s : ℝ} (hs : 0<s) :
    (volume : Measure Plane).real (Metric.closedBall 0 s)≤4*Real.pi*s^2 := by
  have hsub : Metric.closedBall (0 : Plane) s⊆Metric.ball 0 (2*s) :=
    Metric.closedBall_subset_ball (by linarith)
  have hh := ENNReal.toReal_mono (Metric.isBounded_ball.measure_lt_top.ne :
    (volume : Measure Plane) (Metric.ball (0 : Plane) (2*s))≠⊤) (measure_mono hsub)
  change volume.real (Metric.closedBall (0 : Plane) s)≤volume.real (Metric.ball 0 (2*s)) at hh
  rw [plane_ball_real (by positivity : 0≤2*s)] at hh
  nlinarith

lemma L2_local_L1 {s : ℝ} (hs : 0<s) (G : Lp Plane 2 (volume : Measure Plane)) :
    (∫ y in Metric.closedBall (0 : Plane) s,‖G y‖)≤2*Real.sqrt Real.pi*s*‖G‖ := by
  let S := Metric.closedBall (0 : Plane) s
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall (0 : Plane) s).measure_lt_top.ne
  have hi : IntegrableOn (fun y ↦ ‖G y‖) S :=
    ((Lp.memLp G).norm.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _)
  have hi₂ := L2_vector_norm_sq_integrable G
  have hh := integral_square_le_mass hi hi₂.integrableOn
  have hE : (∫ y in S,‖G y‖^2)≤‖G‖^2 := by
    rw [L2_vector_norm_sq_integral]
    exact setIntegral_le_integral hi₂ (Eventually.of_forall fun _ ↦ sq_nonneg _)
  have hmass : (volume.restrict S).real univ≤4*Real.pi*s^2 := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using plane_closedBall_mass_le hs
  have hb := hh.trans (mul_le_mul hmass hE
    (integral_nonneg fun _ ↦ sq_nonneg _) (by positivity))
  have hsq := Real.sq_sqrt Real.pi_pos.le
  have hnon : 0≤2*Real.sqrt Real.pi*s*‖G‖ := by positivity
  nlinarith [sq_nonneg ((2*Real.sqrt Real.pi*s)*‖G‖),
    show (2*Real.sqrt Real.pi*s*‖G‖)^2=4*Real.pi*s^2*‖G‖^2 by
      rw [mul_pow,mul_pow,mul_pow,hsq]; ring]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_replacement_bounds :
    ∃ C : ℝ,0<C ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ R δ : ℝ,0<R → 0≤δ → δ≤1 →
    (∀ y∈Metric.ball 0 (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    (∀ᵐ y ∂volume,y∉Metric.ball 0 (8*R) → G y=0) →
    PlaneWeakGradient (Metric.ball 0 (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∃ (w : Lp ℝ 2 (volume : Measure Plane)) (W : Lp Plane 2 (volume : Measure Plane))
      (H : Plane → Plane),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 (8*R)) ∧
      PlaneWeakGradient univ w W ∧ ‖W‖≤8*δ*‖G‖ ∧
      ContDiff ℝ (⊤ : ℕ∞) H ∧
      ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] H ∧
      (∀ x,‖H x‖≤C*R⁻¹*‖G‖) ∧
      (∀ x y,‖H x-H y‖≤C*R⁻¹^2*‖G‖*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := frozen_cmc_gradient_scaled
  refine ⟨144*Real.sqrt Real.pi*C,by positivity,fun p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G hgs hgrad hdiv ↦ ?_⟩
  have hA := (cmcJacobian_contDiff.continuous.comp hp).aestronglyMeasurable (μ := volume)
  have hmem := bounded_coefficient_memLp hA
    (Eventually.of_forall fun y v ↦ cmcJacobian_norm_le (hpb y) v) G
  let F := hmem.toLp (fun y ↦ cmcJacobian (p y) (G y))
  have hF : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (F y))=0 := by
    intro ψ hψ hc hs
    rw [← hdiv ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [hmem.coeFn_toLp] with y hy
    exact congrArg (fderiv ℝ ψ y) hy
  obtain ⟨W,hW,herr,ho,w,hw⟩ := plane_frozen_elliptic_replacement (8*R)
    (cmcJacobian p₀) (by norm_num : (0:ℝ)<1/8)
    (fun v ↦ by simpa only [real_inner_comm] using cmcJacobian_coercive hp₀ v) G F hF
  have hres := frozen_coefficient_local_residual_bound (cmcJacobian p₀)
    hmem.coeFn_toLp hgs hδ hosc
  have herror : ‖W‖≤8*δ*‖G‖ := by nlinarith [herr.trans hres]
  have hn : ‖G-W‖≤9*‖G‖ := (norm_sub_le G W).trans (by
    nlinarith [mul_le_mul_of_nonneg_right hδ1 (norm_nonneg G)])
  have hg' := hgrad.Lp_sub (hw.mono (subset_univ _))
  obtain ⟨H,hH,he,hb,hl⟩ := hbound R hR p₀ hp₀ (u-w) (G-W) hg'
    (fun ψ hψ hc hs ↦ frozen_replacement_divergence (cmcJacobian p₀) ho hψ hc hs)
  have hM : (∫ y in Metric.closedBall (0 : Plane) (8*R),‖(G-W : Lp Plane 2 volume) y‖)≤
      144*Real.sqrt Real.pi*R*‖G‖ := by
    calc
      _ ≤ 2*Real.sqrt Real.pi*(8*R)*‖G-W‖ := L2_local_L1 (by positivity) (G-W)
      _ ≤ 2*Real.sqrt Real.pi*(8*R)*(9*‖G‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring
  refine ⟨w,W,H,hW,hw,herror,hH,he,?_,?_⟩
  · intro x
    calc
      _ ≤ C*R⁻¹^2*(∫ y in Metric.closedBall 0 (8*R),‖(G-W : Lp Plane 2 volume) y‖) := hb x
      _ ≤ C*R⁻¹^2*(144*Real.sqrt Real.pi*R*‖G‖) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by field_simp
  · intro x y
    calc
      _ ≤ C*R⁻¹^3*(∫ z in Metric.closedBall 0 (8*R),‖(G-W : Lp Plane 2 volume) z‖)*‖x-y‖ := hl x y
      _ ≤ C*R⁻¹^3*(144*Real.sqrt Real.pi*R*‖G‖)*‖x-y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by positivity)) (norm_nonneg _)
      _ = _ := by field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem forced_cmc_replacement_bounds :
    ∃ C : ℝ,0<C ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ R δ : ℝ,0<R → 0≤δ → δ≤1 →
    (∀ y∈Metric.ball 0 (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane))
      (G B : Lp Plane 2 (volume : Measure Plane)),
    (∀ᵐ y ∂volume,y∉Metric.ball 0 (8*R) → G y=0) →
    PlaneWeakGradient (Metric.ball 0 (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))=0) →
    ∃ (w : Lp ℝ 2 (volume : Measure Plane))
      (W : Lp Plane 2 (volume : Measure Plane)) (H : Plane → Plane),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 (8*R)) ∧
      PlaneWeakGradient univ w W ∧ ‖W‖≤8*δ*‖G‖+8*‖B‖ ∧
      ContDiff ℝ (⊤ : ℕ∞) H ∧
      ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] H ∧
      (∀ x,‖H x‖≤C*R⁻¹*(‖G‖+‖B‖)) ∧
      (∀ x y,‖H x-H y‖≤C*R⁻¹^2*(‖G‖+‖B‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := frozen_cmc_gradient_scaled
  refine ⟨144*Real.sqrt Real.pi*C,by positivity,
    fun p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G B hgs hgrad hdiv ↦ ?_⟩
  have hA := (cmcJacobian_contDiff.continuous.comp hp).aestronglyMeasurable (μ := volume)
  have hmem := bounded_coefficient_memLp hA
    (Eventually.of_forall fun y v ↦ cmcJacobian_norm_le (hpb y) v) G
  let F₀ := hmem.toLp (fun y ↦ cmcJacobian (p y) (G y))
  let F := F₀-B
  have hF : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (F y))=0 := by
    intro ψ hψ hc hs
    rw [← hdiv ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub F₀ B,hmem.coeFn_toLp] with y hy hz
    change F y=F₀ y-B y at hy
    change F₀ y=cmcJacobian (p y) (G y) at hz
    rw [hy,hz]
  obtain ⟨W,hW,herr,ho,w,hw⟩ := plane_frozen_elliptic_replacement (8*R)
    (cmcJacobian p₀) (by norm_num : (0:ℝ)<1/8)
    (fun v ↦ by simpa only [real_inner_comm] using cmcJacobian_coercive hp₀ v) G F hF
  have hres := frozen_coefficient_local_residual_bound (cmcJacobian p₀)
    hmem.coeFn_toLp hgs hδ hosc
  have hres' : ‖(cmcJacobian p₀).compLpL 2 volume G-F‖≤δ*‖G‖+‖B‖ := by
    dsimp only [F]
    rw [sub_sub_eq_add_sub,add_sub_right_comm]
    apply (norm_add_le _ _).trans
    exact add_le_add hres le_rfl
  have herror : ‖W‖≤8*δ*‖G‖+8*‖B‖ := by nlinarith [herr.trans hres']
  have hn : ‖G-W‖≤9*(‖G‖+‖B‖) := (norm_sub_le G W).trans (by
    nlinarith [mul_le_mul_of_nonneg_right hδ1 (norm_nonneg G),norm_nonneg B])
  have hg' := hgrad.Lp_sub (hw.mono (subset_univ _))
  obtain ⟨H,hH,he,hb,hl⟩ := hbound R hR p₀ hp₀ (u-w) (G-W) hg'
    (fun ψ hψ hc hs ↦ frozen_replacement_divergence (cmcJacobian p₀) ho hψ hc hs)
  have hM : (∫ y in Metric.closedBall (0 : Plane) (8*R),‖(G-W : Lp Plane 2 volume) y‖)≤
      144*Real.sqrt Real.pi*R*(‖G‖+‖B‖) := by
    calc
      _ ≤ 2*Real.sqrt Real.pi*(8*R)*‖G-W‖ := L2_local_L1 (by positivity) (G-W)
      _ ≤ 2*Real.sqrt Real.pi*(8*R)*(9*(‖G‖+‖B‖)) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring
  refine ⟨w,W,H,hW,hw,herror,hH,he,?_,?_⟩
  · intro x
    calc
      _ ≤ C*R⁻¹^2*(∫ y in Metric.closedBall 0 (8*R),‖(G-W : Lp Plane 2 volume) y‖) := hb x
      _ ≤ C*R⁻¹^2*(144*Real.sqrt Real.pi*R*(‖G‖+‖B‖)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by field_simp
  · intro x y
    calc
      _ ≤ C*R⁻¹^3*(∫ z in Metric.closedBall 0 (8*R),‖(G-W : Lp Plane 2 volume) z‖)*‖x-y‖ := hl x y
      _ ≤ C*R⁻¹^3*(144*Real.sqrt Real.pi*R*(‖G‖+‖B‖))*‖x-y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by positivity)) (norm_nonneg _)
      _ = _ := by field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_L2_sub_const_integrable (G : Lp Plane 2 (volume : Measure Plane))
    (q : Plane) (ρ : ℝ) :
    IntegrableOn (fun y ↦ ‖G y-q‖^2) (Metric.ball 0 ρ) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Plane) ρ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hh := ((Lp.memLp G).restrict (Metric.ball 0 ρ)).sub (memLp_const q)
  exact (memLp_two_iff_integrable_sq hh.norm.aestronglyMeasurable).mp hh.norm

end CubicTorus
end
end
end

end OAI
