import Mathlib
import OAI.Geometry.CubicTorus.Estimates.PlaneWeakGradient

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma PlaneWeakGradient.weak_laplacian {S : Set Plane}
    {u : Lp ℝ 2 (volume : Measure Plane)} {G : Lp Plane 2 (volume : Measure Plane)}
    (hu : PlaneWeakGradient S u G)
    (hdiv : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (G y))=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆S) : (∫ y,u y*Δ ψ y)=0 := by
  let b := stdOrthonormalBasis ℝ Plane
  let D (i : Fin (Module.finrank ℝ Plane)) : Plane → ℝ := fun y ↦ fderiv ℝ ψ y (b i)
  have hD (i) : ContDiff ℝ (⊤ : ℕ∞) (D i) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc (i) : HasCompactSupport (D i) := hc.fderiv_apply ℝ (b i)
  have hDs (i) : tsupport (D i)⊆S := (tsupport_fderiv_apply_subset (f := ψ) ℝ (b i)).trans hs
  have hI (i) : Integrable (fun y ↦ u y*fderiv ℝ (D i) y (b i)) :=
    L2_scalar_test_integrable u (((hD i).continuous_fderiv (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
      ((hDc i).fderiv_apply ℝ (b i)))
  have hJ (i) : Integrable (fun y ↦ ⟪G y,b i⟫*D i y) := by
    have hh := L2_vector_test_integrable G
      (((hD i).continuous.smul continuous_const).memLp_of_hasCompactSupport (hDc i).smul_right :
        MemLp (fun y ↦ D i y • b i) 2 volume)
    simpa only [Pi.smul_def',inner_smul_right,mul_comm] using hh
  have he (y : Plane) : (∑ i,⟪G y,b i⟫*D i y)=fderiv ℝ ψ y (G y) := by
    simpa only [D,inner_gradient_right,conj_trivial] using
      b.sum_inner_mul_inner (G y) (gradient ψ y)
  simp_rw [laplacian_eq_sum_directional hψ,Finset.mul_sum]
  change (∫ y,∑ i,u y*fderiv ℝ (D i) y (b i))=0
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hI i)]
  have hW (i) := hu (b i) (D i) (hD i) (hDc i) (hDs i)
  calc
    _ = -∑ i, ∫ y,⟪G y,b i⟫*D i y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact (neg_eq_iff_eq_neg.mpr (hW i)).symm
    _ = -(∫ y,∑ i,⟪G y,b i⟫*D i y) := by rw [integral_finsetSum Finset.univ (fun i _ ↦ hJ i)]
    _ = -(∫ y,fderiv ℝ ψ y (G y)) := by simp_rw [he]
    _ = 0 := by rw [hdiv ψ hψ hc hs,neg_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_constant_operator_coercive (A : Plane →L[ℝ] Plane) {c : ℝ}
    (hc : ∀ v : Plane,c*‖v‖^2≤⟪A v,v⟫)
    (G : Lp Plane 2 (volume : Measure Plane)) :
    c*‖G‖^2≤⟪A.compLpL 2 volume G,G⟫ := by
  rw [← real_inner_self_eq_norm_sq G,L2.inner_def,L2.inner_def,← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) G G).const_mul c)
    (L2.integrable_inner (𝕜 := ℝ) (A.compLpL 2 volume G) G)
  filter_upwards [A.coeFn_compLpL G] with y hy
  rw [hy,real_inner_self_eq_norm_sq]
  exact hc (G y)

lemma hilbert_coercive_replacement {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (K : Submodule ℝ X)
    [hK : IsClosed (K : Set X)] (L : X →L[ℝ] X) {c : ℝ}
    (hc : 0<c) (hL : ∀ v : X,c*‖v‖^2≤⟪L v,v⟫) (G : X) :
    ∃ W : X, W∈K ∧ c*‖W‖≤‖L G‖ ∧ ∀ F∈K,⟪L (G-W),F⟫=0 := by
  let B : K →L[ℝ] K →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (L.comp K.subtypeL) K.subtypeL
  have hb (x y : K) : B x y=⟪L x,(y : X)⟫ := rfl
  have hB : IsCoercive B := by
    refine ⟨c,hc,fun x ↦ ?_⟩
    rw [hb, ← Submodule.norm_coe x]
    simpa only [pow_two,mul_assoc] using hL (x : X)
  let f : K := K.orthogonalProjectionOnto (L G)
  let z : K := hB.continuousLinearEquivOfBilin.symm f
  let W : X := z
  have he (y : K) : ⟪L W,(y : X)⟫=⟪L G,(y : X)⟫ := by
    have hh := hB.continuousLinearEquivOfBilin_apply z y
    have hz : hB.continuousLinearEquivOfBilin z=f := hB.continuousLinearEquivOfBilin.apply_symm_apply f
    rw [hz,hb] at hh
    have hp := K.starProjection_inner_eq_zero (L G) (y : X) y.property
    rw [inner_sub_left] at hp
    exact hh.symm.trans (by exact (sub_eq_zero.mp hp).symm)
  have hbound : c*‖W‖≤‖L G‖ := by
    by_cases hz : ‖W‖=0
    · simp only [hz,mul_zero]
      positivity
    · have hpos : 0<‖W‖ := lt_of_le_of_ne (norm_nonneg W) (Ne.symm hz)
      apply (mul_le_mul_iff_left₀ hpos).mp
      calc
        (c*‖W‖)*‖W‖=c*‖W‖^2 := by ring
        _ ≤ ⟪L W,W⟫ := hL W
        _ = ⟪L G,W⟫ := he z
        _ ≤ ‖L G‖*‖W‖ := real_inner_le_norm _ _
  refine ⟨W,z.property,hbound,?_⟩
  intro F hF
  rw [map_sub,inner_sub_left,he ⟨F,hF⟩,sub_self]

theorem plane_constant_elliptic_replacement (R : ℝ) (A : Plane →L[ℝ] Plane)
    {c : ℝ} (hc : 0<c) (hA : ∀ v : Plane,c*‖v‖^2≤⟪A v,v⟫)
    (G : Lp Plane 2 (volume : Measure Plane)) :
    ∃ W : Lp Plane 2 (volume : Measure Plane),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 R) ∧
      c*‖W‖≤‖A‖*‖G‖ ∧
      (∀ F∈zeroBoundaryGradientSpace (Metric.ball 0 R),
        ⟪A.compLpL 2 volume (G-W),F⟫=0) ∧
      ∃ w : Lp ℝ 2 (volume : Measure Plane), PlaneWeakGradient univ w W := by
  let K := zeroBoundaryGradientSpace (Metric.ball (0 : Plane) R)
  let : IsClosed (K : Set (Lp Plane 2 (volume : Measure Plane))) :=
    zeroBoundaryGradientSpace_isClosed _
  obtain ⟨W,hW,hb,ho⟩ := hilbert_coercive_replacement K (A.compLpL 2 volume) hc
    (L2_constant_operator_coercive A hA) G
  obtain ⟨w,hw,_⟩ := zeroBoundaryGradientSpace_primitive hW
  exact ⟨W,hW,hb.trans (A.norm_compLp_le G),ho,w,hw⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_divergence_orthogonal {S : Set Plane}
    {F : Lp Plane 2 (volume : Measure Plane)}
    (hF : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (F y))=0) :
    ∀ W∈zeroBoundaryGradientSpace S,⟪F,W⟫=0 := by
  intro W hW
  obtain ⟨ψ,hψ,hc,hs,hlim⟩ := zeroBoundaryGradientSpace_approximation hW
  have he (i : ℕ) : ⟪F,(compact_C1_gradient_memLp ((hψ i).of_le (by simp))
      (hc i)).toLp (gradient (ψ i))⟫=0 := by
    rw [L2_pair_gradient_test ((hψ i).of_le (by simp)) (hc i)]
    exact hF (ψ i) (hψ i) (hc i) (hs i)
  exact tendsto_nhds_unique
    ((tendsto_const_nhds (x := F)).inner (𝕜 := ℝ) hlim |>.congr' (Eventually.of_forall he))
    tendsto_const_nhds

lemma hilbert_coercive_replacement_error {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (K : Submodule ℝ X) (L : X →L[ℝ] X) {c : ℝ}
    (hL : ∀ v : X,c*‖v‖^2≤⟪L v,v⟫) {G W F : X}
    (hW : W∈K) (ho : ∀ V∈K,⟪L (G-W),V⟫=0)
    (hF : ∀ V∈K,⟪F,V⟫=0) : c*‖W‖≤‖L G-F‖ := by
  have he : ⟪L W,W⟫=⟪L G-F,W⟫ := by
    have hh := ho W hW
    rw [map_sub,inner_sub_left] at hh
    rw [inner_sub_left,hF W hW,sub_zero]
    exact (sub_eq_zero.mp hh).symm
  by_cases hz : ‖W‖=0
  · simp only [hz,mul_zero]
    exact norm_nonneg _
  · have hp : 0<‖W‖ := lt_of_le_of_ne (norm_nonneg W) (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      (c*‖W‖)*‖W‖=c*‖W‖^2 := by ring
      _ ≤ ⟪L W,W⟫ := hL W
      _ = ⟪L G-F,W⟫ := he
      _ ≤ ‖L G-F‖*‖W‖ := real_inner_le_norm _ _

theorem plane_frozen_elliptic_replacement (R : ℝ) (A : Plane →L[ℝ] Plane)
    {c : ℝ} (hc : 0<c) (hA : ∀ v : Plane,c*‖v‖^2≤⟪A v,v⟫)
    (G F : Lp Plane 2 (volume : Measure Plane))
    (hF : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (F y))=0) :
    ∃ W : Lp Plane 2 (volume : Measure Plane),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 R) ∧
      c*‖W‖≤‖A.compLpL 2 volume G-F‖ ∧
      (∀ V∈zeroBoundaryGradientSpace (Metric.ball 0 R),
        ⟪A.compLpL 2 volume (G-W),V⟫=0) ∧
      ∃ w : Lp ℝ 2 (volume : Measure Plane), PlaneWeakGradient univ w W := by
  obtain ⟨W,hW,_hb,ho,w,hw⟩ := plane_constant_elliptic_replacement R A hc hA G
  exact ⟨W,hW,hilbert_coercive_replacement_error _ _
    (L2_constant_operator_coercive A hA) hW ho (L2_divergence_orthogonal hF),ho,w,hw⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma bounded_coefficient_memLp {A : Plane → Plane →L[ℝ] Plane}
    (hA : AEStronglyMeasurable A volume) {C : ℝ}
    (hb : ∀ᵐ y ∂volume,∀ v,‖A y v‖≤C*‖v‖)
    (G : Lp Plane 2 (volume : Measure Plane)) :
    MemLp (fun y ↦ A y (G y)) 2 volume := by
  apply ((Lp.memLp G).norm.const_smul C).mono'
  · exact (ContinuousLinearMap.id ℝ (Plane →L[ℝ] Plane)).aestronglyMeasurable_comp₂ hA
      (Lp.aestronglyMeasurable G)
  · filter_upwards [hb] with y hy
    exact hy (G y)

lemma Lp.norm_le_mul_of_ae {G F : Lp Plane 2 (volume : Measure Plane)}
    {C : ℝ} (hC : 0≤C) (h : ∀ᵐ y ∂volume,‖F y‖≤C*‖G y‖) :
    ‖F‖≤C*‖G‖ := by
  calc
    _ ≤ ‖C • G‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [h,Lp.coeFn_smul C G] with y hy hy'
      rw [hy']
      simpa only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hC] using hy
    _ = C*‖G‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]

lemma frozen_coefficient_residual_bound {A : Plane → Plane →L[ℝ] Plane}
    (A₀ : Plane →L[ℝ] Plane) {G F : Lp Plane 2 (volume : Measure Plane)}
    (hF : (F : Plane → Plane)=ᵐ[volume] (fun y ↦ A y (G y)))
    {δ : ℝ} (hδ : 0≤δ) (hA : ∀ᵐ y ∂volume,‖A₀-A y‖≤δ) :
    ‖A₀.compLpL 2 volume G-F‖≤δ*‖G‖ := by
  apply Lp.norm_le_mul_of_ae hδ
  filter_upwards [Lp.coeFn_sub (A₀.compLpL 2 volume G) F,
    A₀.coeFn_compLpL G,hF,hA] with y hy hz hf ha
  simp only [Pi.sub_apply] at hy
  rw [hy,hz,hf,← sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

lemma frozen_coefficient_local_residual_bound {A : Plane → Plane →L[ℝ] Plane}
    (A₀ : Plane →L[ℝ] Plane) {G F : Lp Plane 2 (volume : Measure Plane)}
    (hF : (F : Plane → Plane)=ᵐ[volume] (fun y ↦ A y (G y)))
    {S : Set Plane} (hG : ∀ᵐ y ∂volume,y∉S → G y=0)
    {δ : ℝ} (hδ : 0≤δ) (hA : ∀ y∈S,‖A₀-A y‖≤δ) :
    ‖A₀.compLpL 2 volume G-F‖≤δ*‖G‖ := by
  apply Lp.norm_le_mul_of_ae hδ
  filter_upwards [Lp.coeFn_sub (A₀.compLpL 2 volume G) F,
    A₀.coeFn_compLpL G,hF,hG] with y hy hz hf hg
  simp only [Pi.sub_apply] at hy
  rw [hy,hz,hf,← sub_apply]
  by_cases hys : y∈S
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hA y hys) (norm_nonneg _))
  · rw [hg hys,map_zero,norm_zero,mul_zero]

lemma cmcJacobian_uniform_lipschitz : ∃ L : ℝ,0≤L ∧ ∀ p q : Plane,
    ‖p‖≤1 → ‖q‖≤1 → ‖cmcJacobian p-cmcJacobian q‖≤L*‖p-q‖ := by
  obtain ⟨L,hL⟩ := cmcJacobian_contDiff.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Plane) (1 : ℝ)) (isCompact_closedBall (0 : Plane) (1 : ℝ))
  refine ⟨L,L.coe_nonneg,fun p q hp hq ↦ ?_⟩
  exact hL.norm_sub_le (by simpa using hp) (by simpa using hq)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_dist (g : Plane → ℝ) (x y : Plane) :
    dist (gradient g x) (gradient g y)=dist (fderiv ℝ g x) (fderiv ℝ g y) := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.isometry.dist_eq _ _

theorem WeakCMCGraph.holder_symbol_extension {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R α C : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (hC : 0≤C)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤C*(dist x y)^α) :
    ∃ (p : Plane → Plane) (D : ℝ),Continuous p ∧ (∀ y,‖p y‖≤1) ∧ 0≤D ∧
      (∀ y∈Metric.ball (0 : Plane) (R/2),p y=gradient g y) ∧
      (∀ x∈Metric.ball (0 : Plane) (R/2),∀ y∈Metric.ball (0 : Plane) (R/2),
        ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α) := by
  obtain ⟨p,C',hpc,hpb,_,hpe,_⟩ := hw.gradient_difference_data hg hK hR hgc
  obtain ⟨L,hL,hLip⟩ := cmcJacobian_uniform_lipschitz
  have he (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/2)) : p y=gradient g y := by
    have hy' : ‖y‖<R/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact hpe y hy'.le
  refine ⟨p,L*C,hpc,hpb,mul_nonneg hL hC,he,?_⟩
  intro x hx y hy
  have hsub : Metric.ball (0 : Plane) (R/2)⊆Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  calc
    _ ≤ L*‖p x-p y‖ := hLip _ _ (hpb x) (hpb y)
    _ = L*dist (fderiv ℝ g x) (fderiv ℝ g y) := by
      rw [he x hx,he y hy,← dist_eq_norm,plane_gradient_dist]
    _ ≤ L*(C*(dist x y)^α) := mul_le_mul_of_nonneg_left
      (hHolder x (hsub hx) y (hsub hy)) hL
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def cmcStretch (p : Plane) : Plane →L[ℝ] Plane :=
  ContinuousLinearMap.id ℝ Plane+(cmcWeight p+1)⁻¹ • (innerSL ℝ p).smulRight p

def cmcCompress (p : Plane) : Plane →L[ℝ] Plane :=
  ContinuousLinearMap.id ℝ Plane-(cmcWeight p*(cmcWeight p+1))⁻¹ • (innerSL ℝ p).smulRight p

lemma cmcStretch_apply (p v : Plane) :
    cmcStretch p v=v+((cmcWeight p+1)⁻¹*⟪p,v⟫) • p := by
  simp only [cmcStretch,add_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcCompress_apply (p v : Plane) :
    cmcCompress p v=v-((cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫) • p := by
  simp only [cmcCompress,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcCompress_stretch (p v : Plane) : cmcCompress p (cmcStretch p v)=v := by
  rw [cmcCompress_apply,cmcStretch_apply,inner_add_right,inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hp := cmcWeight_sq p
  have hw := (cmcWeight_pos p).ne'
  have hw1 : cmcWeight p+1≠0 := by have := cmcWeight_pos p; linarith
  have he : (cmcWeight p*(cmcWeight p+1))⁻¹*
      (⟪p,v⟫+(cmcWeight p+1)⁻¹*⟪p,v⟫*‖p‖^2)=
      (cmcWeight p+1)⁻¹*⟪p,v⟫ := by
    rw [show ‖p‖^2=(cmcWeight p)^2-1 by linarith]
    field_simp
    ring
  rw [he,add_sub_cancel_right]

lemma cmcStretch_compress (p v : Plane) : cmcStretch p (cmcCompress p v)=v := by
  rw [cmcStretch_apply,cmcCompress_apply,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hp := cmcWeight_sq p
  have hw := (cmcWeight_pos p).ne'
  have hw1 : cmcWeight p+1≠0 := by have := cmcWeight_pos p; linarith
  have he : (cmcWeight p+1)⁻¹*
      (⟪p,v⟫-(cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫*‖p‖^2)=
      (cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫ := by
    rw [show ‖p‖^2=(cmcWeight p)^2-1 by linarith]
    field_simp
    ring
  rw [he,sub_add_cancel]

def cmcMetricEquiv (p : Plane) : Plane ≃L[ℝ] Plane :=
  { cmcCompress p with
    invFun := cmcStretch p
    left_inv := cmcStretch_compress p
    right_inv := cmcCompress_stretch p
    continuous_toFun := (cmcCompress p).continuous
    continuous_invFun := (cmcStretch p).continuous }

lemma cmcCompress_symm (p u v : Plane) : ⟪cmcCompress p u,v⟫=⟪u,cmcCompress p v⟫ := by
  simp only [cmcCompress_apply,inner_sub_left,inner_sub_right,inner_smul_left,
    inner_smul_right,conj_trivial,real_inner_comm u p]
  ring

lemma cmcStretch_symm (p u v : Plane) : ⟪cmcStretch p u,v⟫=⟪u,cmcStretch p v⟫ := by
  simp only [cmcStretch_apply,inner_add_left,inner_add_right,inner_smul_left,
    inner_smul_right,conj_trivial,real_inner_comm u p]
  ring

lemma cmcCompress_sq (p v : Plane) :
    cmcCompress p (cmcCompress p v)=cmcWeight p • cmcJacobian p v := by
  rw [cmcCompress_apply,cmcCompress_apply,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq,cmcJacobian_apply,smul_sub,smul_smul,smul_smul]
  have hp := cmcWeight_sq p
  have hw := (cmcWeight_pos p).ne'
  have hw1 : cmcWeight p+1≠0 := by have := cmcWeight_pos p; linarith
  rw [mul_inv_cancel₀ hw,one_smul,sub_sub]
  rw [← add_smul]
  congr 1
  congr 1
  rw [show ‖p‖^2=(cmcWeight p)^2-1 by linarith]
  field_simp
  ring

lemma cmcJacobian_compress (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • cmcCompress p (cmcCompress p v) := by
  rw [cmcCompress_sq,smul_smul,inv_mul_cancel₀ (cmcWeight_pos p).ne',one_smul]

lemma cmcStretch_jacobian (p v : Plane) :
    cmcStretch p (cmcJacobian p v)=(cmcWeight p)⁻¹ • cmcCompress p v := by
  rw [cmcJacobian_compress,map_smul,cmcStretch_compress]

lemma cmcStretch_norm {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcStretch p v‖≤2*‖v‖ := by
  have hw := cmcWeight_ge_one p
  have h0 : 0<cmcWeight p+1 := by linarith
  have hi : (cmcWeight p+1)⁻¹≤1 := (inv_le_one₀ h0).mpr (by linarith)
  rw [cmcStretch_apply]
  calc
    _ ≤ ‖v‖+‖((cmcWeight p+1)⁻¹*⟪p,v⟫) • p‖ := norm_add_le _ _
    _ = ‖v‖+(cmcWeight p+1)⁻¹*|⟪p,v⟫| *‖p‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr h0.le)]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add le_rfl
      apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hi) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
        (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

lemma cmcCompress_norm {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcCompress p v‖≤2*‖v‖ := by
  have hw := cmcWeight_ge_one p
  have h0 : 0<cmcWeight p*(cmcWeight p+1) := by positivity
  have hi : (cmcWeight p*(cmcWeight p+1))⁻¹≤1 := (inv_le_one₀ h0).mpr (by nlinarith)
  rw [cmcCompress_apply]
  calc
    _ ≤ ‖v‖+‖((cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = ‖v‖+(cmcWeight p*(cmcWeight p+1))⁻¹*|⟪p,v⟫| *‖p‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr h0.le)]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add le_rfl
      apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hi) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
        (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeChangeFactor (L : Plane ≃L[ℝ] Plane) : ℝ≥0 :=
  addHaarScalarFactor (volume.map L) (volume : Measure Plane)

lemma planeChangeFactor_pos (L : Plane ≃L[ℝ] Plane) : 0<planeChangeFactor L := by
  let : (volume.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  exact addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

lemma planeChange_map (L : Plane ≃L[ℝ] Plane) :
    volume.map L=(planeChangeFactor L : ℝ≥0∞) • (volume : Measure Plane) := by
  let : (volume.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  exact isAddLeftInvariant_eq_smul _ _

lemma planeChange_integral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Plane ≃L[ℝ] Plane) (f : Plane → X) :
    (∫ y,f (L y))=(planeChangeFactor L : ℝ) • ∫ y,f y := by
  have he := L.toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  change (∫ y,f y ∂volume.map L)=(∫ y,f (L y)) at he
  rw [← he,planeChange_map,integral_smul_measure]
  simp

lemma planeChange_memLp {X : Type*} [NormedAddCommGroup X]
    (L : Plane ≃L[ℝ] Plane) {f : Plane → X} {p : ℝ≥0∞}
    (hf : MemLp f p volume) : MemLp (f ∘ L) p volume := by
  apply L.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.mp
  change MemLp f p (volume.map L)
  rw [planeChange_map]
  exact hf.smul_measure ENNReal.coe_ne_top

lemma planeChange_ae (L : Plane ≃L[ℝ] Plane) {f g : Plane → ℝ}
    (h : f=ᵐ[volume] g) : (f ∘ L)=ᵐ[volume] (g ∘ L) := by
  apply ae_eq_comp L.continuous.measurable.aemeasurable
  rw [planeChange_map]
  exact ae_smul_measure h (planeChangeFactor L : ℝ≥0∞)

lemma PlaneWeakGradient.comp_selfAdjoint {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (L : Plane ≃L[ℝ] Plane)
    (hL : ∀ a b : Plane,⟪L a,b⟫=⟪a,L b⟫) :
    PlaneWeakGradient (L ⁻¹' S) (u ∘ L) (fun y ↦ L (G (L y))) := by
  intro v ψ hψ hc hs
  let φ : Plane → ℝ := ψ ∘ L.symm
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp L.symm.contDiff
  have hφc : HasCompactSupport φ := hc.comp_homeomorph L.symm.toHomeomorph
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ L.symm.toHomeomorph)⊆S
    rw [tsupport_comp_eq_preimage ψ L.symm.toHomeomorph]
    intro z hz
    have hh : L (L.symm z)∈S := hs hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (z : Plane) : fderiv ℝ φ z (L v)=fderiv ℝ ψ (L.symm z) v := by
    rw [fderiv_comp z (hψ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.coe_comp,Function.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  have hh := h (L v) φ hφ hφc hφs
  have he (z : Plane) : ⟪G z,L v⟫*φ z=⟪L (G z),v⟫*ψ (L.symm z) := by
    rw [hL]; rfl
  simp_rw [he,hd] at hh
  have h₁ := planeChange_integral L (fun z ↦ ⟪L (G z),v⟫*ψ (L.symm z))
  have h₂ := planeChange_integral L (fun z ↦ u z*fderiv ℝ ψ (L.symm z) v)
  simp only [ContinuousLinearEquiv.symm_apply_apply,smul_eq_mul] at h₁ h₂
  change (∫ y,⟪L (G (L y)),v⟫*ψ y)= -(∫ y,u (L y)*fderiv ℝ ψ y v)
  rw [h₁,h₂,hh,mul_neg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma cmcMetricEquiv_apply (p v : Plane) : cmcMetricEquiv p v=cmcCompress p v := rfl
lemma cmcMetricEquiv_symm_apply (p v : Plane) : (cmcMetricEquiv p).symm v=cmcStretch p v := rfl

lemma frozen_cmc_divergence_change {S : Set Plane} (p : Plane) (G : Plane → Plane)
    (hdiv : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G y)))=0) :
    ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆(cmcMetricEquiv p) ⁻¹' S →
      (∫ y,fderiv ℝ ψ y (cmcMetricEquiv p (G (cmcMetricEquiv p y))))=0 := by
  let L := cmcMetricEquiv p
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
  have hd (z : Plane) : fderiv ℝ φ z (cmcJacobian p (G z))=
      (cmcWeight p)⁻¹*fderiv ℝ ψ (L.symm z) (L (G z)) := by
    rw [fderiv_comp z (hψ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.coe_comp,Function.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    change fderiv ℝ ψ (L.symm z) (cmcStretch p (cmcJacobian p (G z)))=_
    rw [cmcStretch_jacobian,map_smul,smul_eq_mul]
    rfl
  have hh := hdiv φ hφ hφc hφs
  simp_rw [hd] at hh
  rw [integral_const_mul] at hh
  have hh0 : (∫ z,fderiv ℝ ψ (L.symm z) (L (G z)))=0 :=
    (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (cmcWeight_pos p).ne')
  have he := planeChange_integral L (fun z ↦ fderiv ℝ ψ (L.symm z) (L (G z)))
  simp only [ContinuousLinearEquiv.symm_apply_apply,hh0,smul_zero] at he
  exact he

theorem frozen_cmc_weak_harmonic {S : Set Plane} (p : Plane)
    {u : Lp ℝ 2 (volume : Measure Plane)} {G : Lp Plane 2 (volume : Measure Plane)}
    (hgrad : PlaneWeakGradient S u G)
    (hdiv : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G y)))=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆(cmcMetricEquiv p) ⁻¹' S) :
    (∫ y,u (cmcMetricEquiv p y)*Δ ψ y)=0 := by
  let L := cmcMetricEquiv p
  have hu := planeChange_memLp L (Lp.memLp u)
  have hG := L.toContinuousLinearMap.comp_memLp' (planeChange_memLp L (Lp.memLp G))
  let u' := hu.toLp ((u : Plane → ℝ) ∘ L)
  let G' := hG.toLp (fun y ↦ L (G (L y)))
  have hraw := hgrad.comp_selfAdjoint L (cmcCompress_symm p)
  have hg' : PlaneWeakGradient (L ⁻¹' S) u' G' := hraw.congr hu.coeFn_toLp hG.coeFn_toLp
  have hd' : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ⊆L ⁻¹' S → (∫ y,fderiv ℝ φ y (G' y))=0 := by
    intro φ hφ hφc hφs
    have hh := frozen_cmc_divergence_change p (G : Plane → Plane) hdiv φ hφ hφc hφs
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with y hy
    exact congrArg (fderiv ℝ φ y) hy
  have hh := hg'.weak_laplacian hd' hψ hc hs
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with y hy
  exact congrArg (fun a : ℝ ↦ a*Δ ψ y) hy.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

theorem plane_L2_weak_harmonic_smooth {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Plane → ℝ, MemLp f 2 volume →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,f y*Δ ψ y)=0) →
      ∃ u : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) u ∧
        f=ᵐ[volume.restrict (Metric.ball 0 R)] u ∧
        ∀ x y : Plane,‖fderiv ℝ u x-fderiv ℝ u y‖≤
          C*(∫ z in Metric.closedBall 0 (4*R),‖f z‖)*‖x-y‖ := by
  obtain ⟨C,hC,hregular⟩ := plane_weak_harmonic_smooth_representative hR
  refine ⟨C,hC,fun f hf hw ↦ ?_⟩
  let S := Metric.closedBall (0 : Plane) (4*R)
  let F : Plane → ℝ := S.indicator f
  have hfi : IntegrableOn f S := (hf.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall _ _)
  have hF : Integrable F := hfi.integrable_indicator measurableSet_closedBall
  have hFw : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
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
  obtain ⟨u,hu,he,hb⟩ := hregular F hF hFw
  refine ⟨u,hu,?_,?_⟩
  · filter_upwards [he,ae_restrict_mem measurableSet_ball] with y hy hys
    have hS : y∈S := Metric.ball_subset_closedBall
      ((Metric.ball_subset_ball (by linarith : R≤4*R)) hys)
    simpa only [F,indicator_of_mem hS] using hy
  · have heI : (∫ z,‖F z‖)=∫ z in S,‖f z‖ := by
      rw [← integral_indicator measurableSet_closedBall]
      apply integral_congr_ae
      filter_upwards [] with z
      change ‖S.indicator f z‖=S.indicator (fun z ↦ ‖f z‖) z
      by_cases hz : z∈S <;> simp [hz]
    simpa only [heI] using hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_weak_gradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (S : Set Plane) : PlaneWeakGradient S f (gradient f) := by
  intro v ψ hψ hc _hs
  have hi₁ : Integrable (fun y ↦ fderiv ℝ f y v*ψ y) :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hi₂ : Integrable (fun y ↦ f y*fderiv ℝ ψ y v) :=
    (hf.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun _ _ ↦ (hf.differentiable (by simp)).differentiableAt)
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [inner_gradient_left,neg_neg] using congrArg Neg.neg hh.symm

lemma PlaneWeakGradient.local_congr {S : Set Plane} (hS : MeasurableSet S)
    {u u' : Plane → ℝ} {G G' : Plane → Plane} (h : PlaneWeakGradient S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradient S u' G' := by
  have hu' := (ae_restrict_iff' hS).mp hu
  have hG' := (ae_restrict_iff' hS).mp hG
  intro v ψ hψ hc hs
  have hleft : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply integral_congr_ae
    filter_upwards [hG'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hys (hs hh)),mul_zero,mul_zero]
  have hright : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply integral_congr_ae
    filter_upwards [hu'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hys (hs hh)),zero_apply,mul_zero,mul_zero]
  rw [hleft,hright]
  exact h v ψ hψ hc hs

lemma PlaneWeakGradient.unique {S : Set Plane} (hS : IsOpen S)
    {u : Plane → ℝ} {G H : Plane → Plane}
    (hG : LocallyIntegrable G volume) (hH : LocallyIntegrable H volume)
    (huG : PlaneWeakGradient S u G) (huH : PlaneWeakGradient S u H) :
    G=ᵐ[volume.restrict S] H := by
  have hz := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hG.sub hH).locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · change ∀ᵐ y ∂volume.restrict S, G y = H y
    rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards [hz] with y hy hys
    exact sub_eq_zero.mp (hy hys)
  · have hiG := hG.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    have hiH := hH.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    simp only [Pi.sub_apply,smul_sub,integral_sub hiG hiH]
    apply sub_eq_zero.mpr
    apply ext_inner_left ℝ
    intro v
    rw [← integral_inner hiG v,← integral_inner hiH v]
    simp only [inner_smul_right]
    simp_rw [real_inner_comm (G _) v,real_inner_comm (H _) v]
    simpa only [mul_comm] using (huG v ψ hψ hc hs).trans (huH v ψ hψ hc hs).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma PlaneWeakGradient.mono {S T : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hTS : T⊆S) : PlaneWeakGradient T u G := by
  intro v ψ hψ hc hs
  exact h v ψ hψ hc (hs.trans hTS)

lemma planeChange_ae_prop (L : Plane ≃L[ℝ] Plane) {P : Plane → Prop}
    (hP : ∀ᵐ y ∂volume,P y) : ∀ᵐ y ∂volume,P (L y) := by
  apply ae_of_ae_map L.continuous.measurable.aemeasurable
  rw [planeChange_map]
  exact Measure.ae_smul_measure hP (planeChangeFactor L : ℝ≥0∞)

lemma cmcMetricEquiv_norm {p : Plane} (hp : ‖p‖≤1) (y : Plane) :
    ‖cmcMetricEquiv p y‖≤2*‖y‖ := cmcCompress_norm hp y

lemma cmcMetricEquiv_symm_norm {p : Plane} (hp : ‖p‖≤1) (y : Plane) :
    ‖(cmcMetricEquiv p).symm y‖≤2*‖y‖ := cmcStretch_norm hp y

lemma cmcMetricEquiv_ball {p : Plane} (hp : ‖p‖≤1) (R : ℝ) :
    Metric.ball 0 (4*R)⊆(cmcMetricEquiv p) ⁻¹' Metric.ball 0 (8*R) := by
  intro y hy
  have hy' : ‖y‖<4*R := by simpa only [Metric.mem_ball,dist_zero_right] using hy
  have hh : ‖cmcMetricEquiv p y‖<8*R := (cmcMetricEquiv_norm hp y).trans_lt (by linarith)
  simpa only [mem_preimage,Metric.mem_ball,dist_zero_right] using hh

theorem frozen_cmc_smooth {p : Plane} (hp : ‖p‖≤1) {R : ℝ} (hR : 0<R)
    {u : Lp ℝ 2 (volume : Measure Plane)} {G : Lp Plane 2 (volume : Measure Plane)}
    (hgrad : PlaneWeakGradient (Metric.ball 0 (8*R)) u G)
    (hdiv : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) →
      (∫ y,fderiv ℝ ψ y (cmcJacobian p (G y)))=0) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧
      (u : Plane → ℝ)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] f ∧
      (G : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] gradient f := by
  let L := cmcMetricEquiv p
  have hharm : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,u (L y)*Δ ψ y)=0 := by
    intro ψ hψ hc hs
    exact frozen_cmc_weak_harmonic p hgrad hdiv hψ hc (hs.trans (cmcMetricEquiv_ball hp R))
  obtain ⟨_C,_hC,hsmooth⟩ := plane_L2_weak_harmonic_smooth hR
  obtain ⟨v,hv,he,_hb⟩ := hsmooth ((u : Plane → ℝ) ∘ L)
    (planeChange_memLp L (Lp.memLp u)) hharm
  let f := v ∘ L.symm
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hv.comp L.symm.contDiff
  have he' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) R → u (L y)=v y :=
    (ae_restrict_iff' measurableSet_ball).mp he
  have he'' := planeChange_ae_prop L.symm he'
  have heu : (u : Plane → ℝ)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] f := by
    change ∀ᵐ y ∂volume.restrict (Metric.ball 0 (R/2)),u y=f y
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [he''] with y hy hys
    have hys' : ‖y‖<R/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hys
    have hLy : L.symm y∈Metric.ball (0 : Plane) R := by
      rw [Metric.mem_ball,dist_zero_right]
      exact (cmcMetricEquiv_symm_norm hp y).trans_lt (by linarith)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,f,Function.comp_apply] using hy hLy
  refine ⟨f,hf,heu,?_⟩
  have huG := (hgrad.mono (Metric.ball_subset_ball (by linarith : R/2≤8*R))).local_congr
    measurableSet_ball heu.symm (Filter.EventuallyEq.refl _ _)
  exact huG.unique Metric.isOpen_ball ((Lp.memLp G).locallyIntegrable (by norm_num))
    (C1_gradient_continuous (hf.of_le (by simp))).locallyIntegrable
    (C1_weak_gradient (hf.of_le (by simp)) _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma frozen_replacement_divergence {S : Set Plane} (A : Plane →L[ℝ] Plane)
    {H : Lp Plane 2 (volume : Measure Plane)}
    (ho : ∀ V∈zeroBoundaryGradientSpace S,⟪A.compLpL 2 volume H,V⟫=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆S) : (∫ y,fderiv ℝ ψ y (A (H y)))=0 := by
  have hh : (∫ y,fderiv ℝ ψ y ((A.compLpL 2 volume H) y))=0 := by
    rw [← L2_pair_gradient_test (hψ.of_le (by simp)) hc]
    exact ho _ ((smoothGradientSpace S).le_topologicalClosure ⟨ψ,hψ,hc,hs,rfl⟩)
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLpL H] with y hy
  rw [hy]

theorem cmc_frozen_replacement {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {p₀ : Plane} (hp₀ : ‖p₀‖≤1) {R δ : ℝ}
    (hR : 0<R) (hδ : 0≤δ)
    (hosc : ∀ y∈Metric.ball 0 (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ)
    {u : Lp ℝ 2 (volume : Measure Plane)} {G : Lp Plane 2 (volume : Measure Plane)}
    (hgs : ∀ᵐ y ∂volume,y∉Metric.ball 0 (8*R) → G y=0)
    (hgrad : PlaneWeakGradient (Metric.ball 0 (8*R)) u G)
    (hdiv : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ (w : Lp ℝ 2 (volume : Measure Plane)) (W : Lp Plane 2 (volume : Measure Plane))
      (f : Plane → ℝ),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 (8*R)) ∧
      PlaneWeakGradient univ w W ∧ ‖W‖≤8*δ*‖G‖ ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      ((u-w : Lp ℝ 2 volume) : Plane → ℝ)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] f ∧
      ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] gradient f := by
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
    (cmcJacobian p₀) (by norm_num : (0:ℝ)<1/8) (fun v ↦ by simpa only [real_inner_comm] using cmcJacobian_coercive hp₀ v) G F hF
  have hres := frozen_coefficient_local_residual_bound (cmcJacobian p₀)
    hmem.coeFn_toLp hgs hδ hosc
  have hbound : ‖W‖≤8*δ*‖G‖ := by nlinarith [herr.trans hres]
  have hg' := hgrad.Lp_sub (hw.mono (subset_univ _))
  obtain ⟨f,hf,he,hge⟩ := frozen_cmc_smooth hp₀ hR hg'
    (fun ψ hψ hc hs ↦ frozen_replacement_divergence (cmcJacobian p₀) ho hψ hc hs)
  exact ⟨w,W,f,hW,hw,hbound,hf,he,hge⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
