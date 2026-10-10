import Mathlib
import OAI.Geometry.CubicTorus.Estimates.DifferenceStep

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma differential_integral_restrict {ψ : Plane → ℝ} {S : Set Plane}
    (hs : tsupport ψ⊆S) (F : Plane → Plane) :
    (∫ y in S, fderiv ℝ ψ y (F y))=(∫ y, fderiv ℝ ψ y (F y)) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy (hs hy')),zero_apply]

theorem WeakCMCGraph.linearized_equation {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hcmc : WeakCMCGraph g H (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      (∀ (w : Plane) (ψ : Plane → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), ⟪u y,w⟫*ψ y)=
          -(∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)) ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (gradient g y) (u y)))=0) := by
  obtain ⟨G,C,hGc,hGb,hC,hGeq,henergy⟩ := hcmc.gradient_difference_data hg hK hR hgc
  have hδ : 0<R/4 := by linarith
  obtain ⟨u,φ,_hu,hφ,hw⟩ := vector_L2_difference_subsequence hGc hGb hδ hC v (henergy v hv)
  let t : ℕ → ℝ := fun i ↦ differenceStep (R/4) (φ i)
  let Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))) := fun i ↦
    (vectorDifference_memLp hGc hGb (R/4) (t i) v).toLp (vectorDifference G v (t i))
  have ht (i : ℕ) : t i∈Ioc 0 (R/4) := differenceStep_mem hδ (φ i)
  have htlim : Tendsto t atTop (𝓝[>] 0) := (differenceStep_tendsto hδ).comp hφ.tendsto_atTop
  have hQ (i : ℕ) : (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) (R/4))]
      vectorDifference G v (t i) := (vectorDifference_memLp hGc hGb (R/4) (t i) v).coeFn_toLp
  have hweak : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫) := hw
  have hty (i : ℕ) : ‖t i • v‖≤t i := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (ht i).1]
    exact mul_le_of_le_one_right (ht i).1.le hv
  have hGy (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) : G y=gradient g y := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    linarith
  have hGyt (i : ℕ) (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) :
      G (y+t i • v)=gradient g (y+t i • v) := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans (by linarith [hty i,(ht i).2])
  refine ⟨u,?_,?_⟩
  · intro w ψ hψ hc hs
    rw [vector_weak_quotient_derivative hGc htlim v w hQ hweak hψ hc hs]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈tsupport ψ
    · rw [hGy y (hs hy)]
    · rw [fderiv_of_notMem_tsupport ℝ hy,zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    have hlim := weak_L2_cmc_chain hGc hGb hC (fun i ↦ (ht i).1)
      (tendsto_nhds_of_tendsto_nhdsWithin htlim) v (fun i ↦ henergy v hv (t i) (ht i)) hQ hweak hψ hc
    have hzero (i : ℕ) : (∫ y in Metric.ball 0 (R/4),
        fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (G (y+t i • v))-cmcFlux (G y))))=0 := by
      calc
        _ = ∫ y in Metric.ball 0 (R/4),
            fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := by
          apply setIntegral_congr_fun measurableSet_ball
          intro y hy
          dsimp only
          rw [hGy y hy,hGyt i y hy]
        _ = ∫ y, fderiv ℝ ψ y ((t i)⁻¹ •
            (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := differential_integral_restrict hs _
        _ = (t i)⁻¹*(∫ y, fderiv ℝ ψ y
            (cmcFlux (gradient g (y+t i • v))-cmcFlux (gradient g y))) := by
          simp only [map_smul,smul_eq_mul,integral_const_mul]
        _ = 0 := by
          rw [hcmc.difference_test hg hδ (by linarith [hty i,(ht i).2]) hψ hc hs,mul_zero]
    have he : (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (G y) (u y)))=0 :=
      tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)
    rw [← he]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    dsimp only
    rw [hGy y hy]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.weak_derivative {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      (∀ (w : Plane) (ψ : Plane → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), ⟪u y,w⟫*ψ y)=
          -(∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)) ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (p y) (u y)-
          (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))))=0) := by
  obtain ⟨G,C,hGc,hGb,hC,hGeq,henergy⟩ := hw.gradient_difference_data hg hp hpb hA hB hBb hR hgc
  have hδ : 0<R/4 := by linarith
  obtain ⟨u,φ,_hu,hφ,hwk⟩ := vector_L2_difference_subsequence hGc hGb hδ hC v (henergy v hv)
  let t : ℕ → ℝ := fun i ↦ differenceStep (R/4) (φ i)
  let Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))) := fun i ↦
    (vectorDifference_memLp hGc hGb (R/4) (t i) v).toLp (vectorDifference G v (t i))
  have ht (i : ℕ) : t i∈Ioc 0 (R/4) := differenceStep_mem hδ (φ i)
  have htlim : Tendsto t atTop (𝓝[>] 0) := (differenceStep_tendsto hδ).comp hφ.tendsto_atTop
  have hQ (i : ℕ) : (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) (R/4))]
      vectorDifference G v (t i) := (vectorDifference_memLp hGc hGb (R/4) (t i) v).coeFn_toLp
  have hweak : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫) := hwk
  have hty (i : ℕ) : ‖t i • v‖≤t i := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (ht i).1]
    exact mul_le_of_le_one_right (ht i).1.le hv
  have hGy (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) : G y=gradient g y := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    linarith
  have hGyt (i : ℕ) (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) :
      G (y+t i • v)=gradient g (y+t i • v) := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans (by linarith [hty i,(ht i).2])
  refine ⟨u,?_,?_⟩
  · intro w ψ hψ hc hs
    rw [vector_weak_quotient_derivative hGc htlim v w hQ hweak hψ hc hs]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈tsupport ψ
    · rw [hGy y (hs hy)]
    · rw [fderiv_of_notMem_tsupport ℝ hy,zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    have hlim := weak_L2_linear_cmc_chain hGc hGb hp hpb hA hB
      (hAc.differentiable (by simp)) (hBc.differentiable (by simp))
      (fun i ↦ (ht i).1) htlim v hQ hweak hψ hc
    have hzero (i : ℕ) : (∫ y in Metric.ball 0 (R/4),
        fderiv ℝ ψ y ((t i)⁻¹ • ((cmcJacobian (p (y+t i • v)) (G (y+t i • v))-B (y+t i • v))-
          (cmcJacobian (p y) (G y)-B y))))=0 := by
      calc
        _ = ∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y ((t i)⁻¹ •
            ((cmcJacobian (p (y+t i • v)) (gradient g (y+t i • v))-B (y+t i • v))-
              (cmcJacobian (p y) (gradient g y)-B y))) := by
          apply setIntegral_congr_fun measurableSet_ball
          intro y hy
          dsimp only
          rw [hGy y hy,hGyt i y hy]
        _ = ∫ y, fderiv ℝ ψ y ((t i)⁻¹ •
            ((cmcJacobian (p (y+t i • v)) (gradient g (y+t i • v))-B (y+t i • v))-
              (cmcJacobian (p y) (gradient g y)-B y))) := differential_integral_restrict hs _
        _ = (t i)⁻¹*(∫ y, fderiv ℝ ψ y
            ((cmcJacobian (p (y+t i • v)) (gradient g (y+t i • v))-B (y+t i • v))-
              (cmcJacobian (p y) (gradient g y)-B y))) := by
          simp only [map_smul,smul_eq_mul,integral_const_mul]
        _ = 0 := by
          rw [hw.difference_test hg hp hpb hB.continuous hBb hδ
            (by linarith [hty i,(ht i).2]) hψ hc hs,mul_zero]
    have he : (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (p y) (u y)))+
        (∫ y in Metric.ball 0 (R/4),fderiv ℝ ψ y
          (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (G y)-fderiv ℝ B y v))=0 :=
      tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)
    have hAi := Lp.cmc_differential_integrable hp hpb (R/4) u hψ hc
    have hSc : Continuous (fun y ↦ fderiv ℝ ψ y
        (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (G y)-fderiv ℝ B y v)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply
        ((((hAc.continuous_fderiv (by simp)).clm_apply continuous_const).clm_apply hGc).sub
          ((hBc.continuous_fderiv (by simp)).clm_apply continuous_const))
    have hSi := hSc.continuousOn.integrableOn_compact (μ := (volume : Measure Plane))
      (isCompact_closedBall (0 : Plane) (R/4)) |>.mono_set Metric.ball_subset_closedBall
    rw [← integral_add hAi hSi] at he
    rw [← he]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    dsimp only
    rw [hGy y hy]
    simp only [map_sub]
    ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_gradient_continuous {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hf.continuous_fderiv (by simp))

lemma plane_gradient_support {f : Plane → ℝ} : tsupport (gradient f)⊆tsupport f := by
  exact (tsupport_comp_subset (g := (InnerProductSpace.toDual ℝ Plane).symm) (by simp) _).trans
    (tsupport_fderiv_subset ℝ)

lemma plane_gradient_compact {f : Plane → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (gradient f) :=
  (hf.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ Plane).symm)

lemma compact_C1_gradient_memLp {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : MemLp (gradient f) 2 :=
  (C1_gradient_continuous hf).memLp_of_hasCompactSupport (plane_gradient_compact hc)

lemma compact_test_poincare (R : ℝ) : ∃ C : ℝ, 0≤C ∧
    ∀ f : Plane → ℝ, ∀ hf : ContDiff ℝ 1 f, ∀ hc : HasCompactSupport f,
      tsupport f⊆Metric.ball 0 R →
      ‖(hf.continuous.memLp_of_hasCompactSupport hc : MemLp f 2).toLp f‖≤
        C*‖(compact_C1_gradient_memLp hf hc).toLp (gradient f)‖ := by
  let A : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Plane) 1
  let B : ℝ≥0∞ := volume (Metric.ball (0 : Plane) R)^(1/2:ℝ)
  have hB : B≠⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  refine ⟨(A:ℝ)*B.toReal,by positivity,?_⟩
  intro f hf hc hs
  have hd := hf.continuous_fderiv (by simp : (1 : WithTop ℕ∞)≠0)
  have hm : MemLp (fderiv ℝ f) 2 := hd.memLp_of_hasCompactSupport (hc.fderiv ℝ)
  have hsub : Function.support (fderiv ℝ f)⊆Metric.ball 0 R :=
    (subset_tsupport (fderiv ℝ f)).trans ((tsupport_fderiv_subset ℝ).trans hs)
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Plane) hf hc
    (p := 1) (p' := 2) (by norm_num) (by simp [Plane]) (by norm_num [Plane])
  have hcomp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Metric.ball 0 R))
    (f := fderiv ℝ f) (p := 1) (q := 2) (by norm_num) hd.aestronglyMeasurable.restrict
  rw [eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := 1) (f := fderiv ℝ f) hd.aestronglyMeasurable hsub,
    eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := 2) (f := fderiv ℝ f) hd.aestronglyMeasurable hsub,Measure.restrict_apply_univ] at hcomp
  norm_num only [ENNReal.toReal_one,ENNReal.toReal_ofNat,div_one] at hcomp
  have hcomp' : eLpNorm (fderiv ℝ f) 1 volume≤eLpNorm (fderiv ℝ f) 2 volume*B := by
    exact hcomp
  have he : eLpNorm f 2 volume ≤ (A:ℝ≥0∞)*(eLpNorm (fderiv ℝ f) 2 volume*B) :=
    hgns.trans (mul_le_mul_right hcomp' _)
  have hgn : eLpNorm (gradient f) 2 volume=eLpNorm (fderiv ℝ f) 2 volume :=
    eLpNorm_congr_norm_ae (C1_gradient_continuous hf).aestronglyMeasurable
      hd.aestronglyMeasurable (ae_of_all _ (plane_gradient_norm f))
  rw [Lp.norm_toLp,Lp.norm_toLp,hgn]
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.mul_ne_top hm.ne hB)) he
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal,mul_assoc,mul_comm,mul_left_comm] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def PlaneWeakGradient (S : Set Plane) (u : Plane → ℝ) (G : Plane → Plane) : Prop :=
  ∀ (v : Plane) (ψ : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ⊆S → (∫ y, ⟪G y,v⟫*ψ y)= -(∫ y,u y*fderiv ℝ ψ y v)

lemma PlaneWeakGradient.congr {S : Set Plane} {u u' : Plane → ℝ} {G G' : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hu : u'=ᵐ[volume] u) (hG : G'=ᵐ[volume] G) :
    PlaneWeakGradient S u' G' := by
  intro v ψ hψ hc hs
  have ha : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) :=
    integral_congr_ae (hG.mono fun _ he ↦ by dsimp only; rw [he])
  have hb : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) :=
    integral_congr_ae (hu.mono fun _ he ↦ by dsimp only; rw [he])
  rw [ha,hb]
  exact h v ψ hψ hc hs

lemma compact_C1_weak_gradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (_hc : HasCompactSupport f) (S : Set Plane) : PlaneWeakGradient S f (gradient f) := by
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

lemma L2_pair_scalar_test {u : Lp ℝ 2 (volume : Measure Plane)} {φ : Plane → ℝ}
    (hφ : MemLp φ 2 volume) : ⟪u,hφ.toLp φ⟫=(∫ y,u y*φ y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with y hy
  simp only [hy,RCLike.inner_apply,conj_trivial]
  ring

lemma L2_pair_vector_test {G : Lp Plane 2 (volume : Measure Plane)} {φ : Plane → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (v : Plane) :
    let hm : MemLp (fun y ↦ φ y • v) 2 volume :=
      (hφ.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right
    ⟪G,hm.toLp (fun y ↦ φ y • v)⟫=(∫ y,⟪G y,v⟫*φ y) := by
  dsimp only
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((hφ.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right :
    MemLp (fun y ↦ φ y • v) 2 volume).coeFn_toLp] with y hy
  simp only [Pi.smul_def'] at hy
  rw [hy,inner_smul_right,mul_comm]

lemma PlaneWeakGradient.L2_limit {S : Set Plane}
    {u : ℕ → Lp ℝ 2 (volume : Measure Plane)} {G : ℕ → Lp Plane 2 (volume : Measure Plane)}
    {u₀ : Lp ℝ 2 (volume : Measure Plane)} {G₀ : Lp Plane 2 (volume : Measure Plane)}
    (hu : Tendsto u atTop (𝓝 u₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (hweak : ∀ i,PlaneWeakGradient S (u i) (G i)) : PlaneWeakGradient S u₀ G₀ := by
  intro v ψ hψ hc hs
  let a : Plane → Plane := fun y ↦ ψ y • v
  have ha : MemLp a 2 volume := (hψ.continuous.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right
  let A := ha.toLp a
  let b : Plane → ℝ := fun y ↦ fderiv ℝ ψ y v
  have hb : MemLp b 2 volume := ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hc.fderiv_apply ℝ v)
  let B := hb.toLp b
  have he (i : ℕ) : ⟪G i,A⟫= -⟪u i,B⟫ := by
    rw [L2_pair_vector_test hψ.continuous hc v,L2_pair_scalar_test hb]
    exact hweak i v ψ hψ hc hs
  have hleft := hG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := A))
  have hright := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := B))).neg
  have hh := tendsto_nhds_unique (hleft.congr' (Eventually.of_forall he)) hright
  rw [L2_pair_vector_test hψ.continuous hc v,L2_pair_scalar_test hb] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_scalar_product {f η : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hf : ContinuousOn f S) (hη : Continuous η)
    (hs : tsupport η⊆S) : Continuous (fun y ↦ f y*η y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact ((hf y (hs hy)).continuousAt (hS.mem_nhds (hs hy))).mul hη.continuousAt
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma C1_local_integration_by_parts {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S) (v : Plane) :
    (∫ y, fderiv ℝ g y v*ψ y)= -(∫ y,g y*fderiv ℝ ψ y v) := by
  have hdf : ContinuousOn (fun y ↦ fderiv ℝ g y v) S :=
    (hgc.continuousOn_fderiv_of_isOpen hS (by simp)).clm_apply continuousOn_const
  have hi₁ : Integrable (fun y ↦ fderiv ℝ g y v*ψ y) :=
    (continuous_local_scalar_product hS hdf hψ.continuous hs).integrable_of_hasCompactSupport hc.mul_left
  have hi₂ : Integrable (fun y ↦ g y*fderiv ℝ ψ y v) :=
    (hg.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ g y*ψ y) :=
    (hg.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun y hy ↦ ((hgc y (hs hy)).contDiffAt (hS.mem_nhds (hs hy))).differentiableAt (by simp))
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [neg_neg] using congrArg Neg.neg hh.symm

lemma C1_mixed_test_identity {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S)
    (v w : Plane) :
    (∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)=
      (∫ y, ⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ ψ y w) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  simp only [inner_gradient_left]
  rw [C1_local_integration_by_parts hS hg hgc (hv.of_le (by simp))
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset (f := ψ) ℝ v).trans hs) w,
    C1_local_integration_by_parts hS hg hgc (hw.of_le (by simp))
    (hc.fderiv_apply ℝ w) ((tsupport_fderiv_apply_subset (f := ψ) ℝ w).trans hs) v]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  rw [fderiv_fderiv_apply hψ,fderiv_fderiv_apply hψ]
  exact (hψ.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma indicator_inner_test_integral {S : Set Plane} (hS : MeasurableSet S)
    (U : Plane → Plane) (v : Plane) (ψ : Plane → ℝ) :
    (∫ y,⟪S.indicator U y,v⟫*ψ y)=(∫ y in S,⟪U y,v⟫*ψ y) := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈S <;> simp [hy]

lemma indicator_differential_integral {S : Set Plane} (hS : MeasurableSet S)
    (U : Plane → Plane) (A : Plane → Plane →L[ℝ] Plane) (ψ : Plane → ℝ) :
    (∫ y,fderiv ℝ ψ y (A y (S.indicator U y)))=
      (∫ y in S,fderiv ℝ ψ y (A y (U y))) := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈S <;> simp [hy]

theorem WeakCMCGraph.scalar_linearized_equation {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hcmc : WeakCMCGraph g H (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ (u : Lp ℝ 2 (volume : Measure Plane)) (U : Lp Plane 2 (volume : Measure Plane)),
      (u : Plane → ℝ)=ᵐ[volume.restrict (Metric.ball 0 (R/4))]
        (fun y ↦ fderiv ℝ g y v) ∧
      PlaneWeakGradient (Metric.ball 0 (R/4)) u U ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y,fderiv ℝ ψ y (cmcJacobian (gradient g y) (U y)))=0) := by
  let S : Set Plane := Metric.ball 0 (R/4)
  obtain ⟨F,hF,hlin⟩ := hcmc.linearized_equation hg hK hR hgc v hv
  have hFmem : MemLp (S.indicator (F : Plane → Plane)) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp F)
  let U := hFmem.toLp (S.indicator (F : Plane → Plane))
  let b : ContDiffBump (0 : Plane) := ⟨R/4,R/2,by linarith,by linarith⟩
  let f : Plane → ℝ := fun y ↦ fderiv ℝ g y v*b y
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hfc : Continuous f := continuous_local_scalar_product Metric.isOpen_ball
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const)
    b.continuous hbs
  have hfs : HasCompactSupport f := b.hasCompactSupport.mul_left
  have hfmem : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hfs
  let u := hfmem.toLp f
  have hfe (y : Plane) (hy : y∈S) : f y=fderiv ℝ g y v := by
    dsimp only [f]
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),mul_one]
  refine ⟨u,U,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hfmem.coeFn_toLp,ae_restrict_mem (measurableSet_ball : MeasurableSet S)] with y hy hs
    exact hy.trans (hfe y hs)
  · intro w ψ hψ hc hs
    have hψs : tsupport ψ⊆Metric.ball 0 R := hs.trans (Metric.ball_subset_ball (by linarith))
    calc
      _ = ∫ y,⟪S.indicator (F : Plane → Plane) y,w⟫*ψ y := by
        apply integral_congr_ae
        filter_upwards [hFmem.coeFn_toLp] with y hy
        rw [hy]
      _ = ∫ y in S,⟪F y,w⟫*ψ y := indicator_inner_test_integral measurableSet_ball _ _ _
      _ = -(∫ y,⟪gradient g y,w⟫*fderiv ℝ ψ y v) := hF w ψ (hψ.of_le (by simp)) hc hs
      _ = -(∫ y,⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
        rw [C1_mixed_test_identity Metric.isOpen_ball hg.continuous hgc hψ hc hψs v w]
      _ = -(∫ y,u y*fderiv ℝ ψ y w) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hfmem.coeFn_toLp] with y hy
        rw [hy,inner_gradient_left]
        by_cases hyS : y∈S
        · rw [hfe y hyS]
        · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hyS (hs h)),zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    calc
      _ = ∫ y,fderiv ℝ ψ y (cmcJacobian (gradient g y) (S.indicator (F : Plane → Plane) y)) := by
        apply integral_congr_ae
        filter_upwards [hFmem.coeFn_toLp] with y hy
        rw [hy]
      _ = ∫ y in S,fderiv ℝ ψ y (cmcJacobian (gradient g y) (F y)) :=
        indicator_differential_integral measurableSet_ball _ _ _
      _ = 0 := hlin ψ (hψ.of_le (by simp)) hc hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.scalar_derivative {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ (u : Lp ℝ 2 (volume : Measure Plane)) (U : Lp Plane 2 (volume : Measure Plane)),
      (u : Plane → ℝ)=ᵐ[volume.restrict (Metric.ball 0 (R/4))]
        (fun y ↦ fderiv ℝ g y v) ∧
      PlaneWeakGradient (Metric.ball 0 (R/4)) u U ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (U y)-
          (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))))=0) := by
  let S : Set Plane := Metric.ball 0 (R/4)
  obtain ⟨F,hF,hlin⟩ := hw.weak_derivative hg hp hpb hA hB hAc hBc hBb hR hgc v hv
  have hFmem : MemLp (S.indicator (F : Plane → Plane)) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp F)
  let U := hFmem.toLp (S.indicator (F : Plane → Plane))
  let b : ContDiffBump (0 : Plane) := ⟨R/4,R/2,by linarith,by linarith⟩
  let f : Plane → ℝ := fun y ↦ fderiv ℝ g y v*b y
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hfc : Continuous f := continuous_local_scalar_product Metric.isOpen_ball
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const)
    b.continuous hbs
  have hfs : HasCompactSupport f := b.hasCompactSupport.mul_left
  have hfmem : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hfs
  let u := hfmem.toLp f
  have hfe (y : Plane) (hy : y∈S) : f y=fderiv ℝ g y v := by
    dsimp only [f]
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),mul_one]
  refine ⟨u,U,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hfmem.coeFn_toLp,ae_restrict_mem (measurableSet_ball : MeasurableSet S)] with y hy hs
    exact hy.trans (hfe y hs)
  · intro w ψ hψ hc hs
    have hψs : tsupport ψ⊆Metric.ball 0 R := hs.trans (Metric.ball_subset_ball (by linarith))
    calc
      _ = ∫ y,⟪S.indicator (F : Plane → Plane) y,w⟫*ψ y := by
        apply integral_congr_ae
        filter_upwards [hFmem.coeFn_toLp] with y hy
        rw [hy]
      _ = ∫ y in S,⟪F y,w⟫*ψ y := indicator_inner_test_integral measurableSet_ball _ _ _
      _ = -(∫ y,⟪gradient g y,w⟫*fderiv ℝ ψ y v) := hF w ψ (hψ.of_le (by simp)) hc hs
      _ = -(∫ y,⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
        rw [C1_mixed_test_identity Metric.isOpen_ball hg.continuous hgc hψ hc hψs v w]
      _ = -(∫ y,u y*fderiv ℝ ψ y w) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hfmem.coeFn_toLp] with y hy
        rw [hy,inner_gradient_left]
        by_cases hyS : y∈S
        · rw [hfe y hyS]
        · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hyS (hs h)),zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    calc
      _ = ∫ y in S,fderiv ℝ ψ y (cmcJacobian (p y) (U y)-
          (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))) :=
        (differential_integral_restrict hs _).symm
      _ = ∫ y in S,fderiv ℝ ψ y (cmcJacobian (p y) (F y)-
          (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hFmem.coeFn_toLp,
          ae_restrict_mem (measurableSet_ball : MeasurableSet S)] with y hy hyS
        rw [hy,Set.indicator_of_mem hyS]
      _ = 0 := hlin ψ (hψ.of_le (by simp)) hc hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_gradient_add {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    gradient (f+g)=gradient f+gradient g := by
  funext x
  simp only [gradient,fderiv_add ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt),map_add,Pi.add_apply]

lemma C1_gradient_smul {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) (a : ℝ) :
    gradient (a • f)=a • gradient f := by
  funext x
  simp only [gradient,fderiv_const_smul ((hf.differentiable (by simp)).differentiableAt),
    map_smul,Pi.smul_apply]

lemma C1_gradient_sub {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    gradient (f-g)=gradient f-gradient g := by
  funext x
  simp only [gradient,fderiv_sub ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt),map_sub,Pi.sub_apply]

def smoothGradientSpace (S : Set Plane) : Submodule ℝ (Lp Plane 2 (volume : Measure Plane)) where
  carrier := {G | ∃ f : Plane → ℝ, ∃ hf : ContDiff ℝ (⊤ : ℕ∞) f,
    ∃ hc : HasCompactSupport f, tsupport f⊆S ∧
      G=(compact_C1_gradient_memLp (hf.of_le (by simp)) hc).toLp (gradient f)}
  zero_mem' := by
    refine ⟨0,contDiff_const,HasCompactSupport.zero,by simp,?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero (E := Plane) (p := 2) (μ := (volume : Measure Plane)),
      (compact_C1_gradient_memLp (f := 0) contDiff_const HasCompactSupport.zero).coeFn_toLp]
      with x hz hx
    rw [hz,hx]
    simp [gradient]
  add_mem' := by
    rintro G K ⟨f,hf,hc,hs,rfl⟩ ⟨g,hg,hgc,hgs,rfl⟩
    refine ⟨f+g,hf.add hg,hc.add hgc,(tsupport_add f g).trans (union_subset hs hgs),?_⟩
    have he := C1_gradient_add (hf.of_le (by simp)) (hg.of_le (by simp))
    apply Lp.ext
    filter_upwards [Lp.coeFn_add
        ((compact_C1_gradient_memLp (hf.of_le (by simp)) hc).toLp (gradient f))
        ((compact_C1_gradient_memLp (hg.of_le (by simp)) hgc).toLp (gradient g)),
      (compact_C1_gradient_memLp (hf.of_le (by simp)) hc).coeFn_toLp,
      (compact_C1_gradient_memLp (hg.of_le (by simp)) hgc).coeFn_toLp,
      (compact_C1_gradient_memLp ((hf.add hg).of_le (by simp)) (hc.add hgc)).coeFn_toLp]
      with x hx hfx hgx hfgx
    rw [hx]
    simp only [Pi.add_def] at hfgx ⊢
    rw [hfgx]
    change _ + _ = gradient (f+g) x
    rw [hfx,hgx,he]
    rfl
  smul_mem' := by
    rintro a G ⟨f,hf,hc,hs,rfl⟩
    have hcf : HasCompactSupport (a • f) := hc.smul_left
    refine ⟨a • f,contDiff_const.smul hf,hcf,
      (tsupport_smul_subset_right (fun _ ↦ a) f).trans hs,?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul a
        ((compact_C1_gradient_memLp (hf.of_le (by simp)) hc).toLp (gradient f)),
      (compact_C1_gradient_memLp (hf.of_le (by simp)) hc).coeFn_toLp,
      (compact_C1_gradient_memLp ((contDiff_const.smul hf).of_le (by simp)) hcf).coeFn_toLp]
      with x hx hfx hax
    rw [hx]
    simp only [Pi.smul_def,Pi.smul_def'] at hax ⊢
    rw [hax]
    change a • _ = gradient (a • f) x
    rw [hfx,C1_gradient_smul (hf.of_le (by simp)) a]
    rfl

def zeroBoundaryGradientSpace (S : Set Plane) : Submodule ℝ (Lp Plane 2 (volume : Measure Plane)) :=
  (smoothGradientSpace S).topologicalClosure

lemma zeroBoundaryGradientSpace_isClosed (S : Set Plane) :
    IsClosed (zeroBoundaryGradientSpace S : Set (Lp Plane 2 (volume : Measure Plane))) :=
  (smoothGradientSpace S).isClosed_topologicalClosure

lemma zeroBoundaryGradientSpace_approximation {S : Set Plane}
    {G : Lp Plane 2 (volume : Measure Plane)} (hG : G∈zeroBoundaryGradientSpace S) :
    ∃ f : ℕ → Plane → ℝ, ∃ hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i),
      ∃ hc : ∀ i, HasCompactSupport (f i),
        (∀ i,tsupport (f i)⊆S) ∧
        Tendsto (fun i ↦ (compact_C1_gradient_memLp ((hf i).of_le (by simp)) (hc i)).toLp
          (gradient (f i))) atTop (𝓝 G) := by
  obtain ⟨F,hF,hlim⟩ := mem_closure_iff_seq_limit.mp hG
  choose f hf hc hs he using hF
  refine ⟨f,hf,hc,hs,?_⟩
  convert hlim using 1
  funext i
  exact (he i).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_test_poincare_difference {R C : ℝ}
    (hP : ∀ f : Plane → ℝ, ∀ hf : ContDiff ℝ 1 f, ∀ hc : HasCompactSupport f,
      tsupport f⊆Metric.ball 0 R →
      ‖(hf.continuous.memLp_of_hasCompactSupport hc : MemLp f 2).toLp f‖≤
        C*‖(compact_C1_gradient_memLp hf hc).toLp (gradient f)‖)
    {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hs : tsupport f⊆Metric.ball 0 R) (hgs : tsupport g⊆Metric.ball 0 R) :
    dist ((hf.continuous.memLp_of_hasCompactSupport hc : MemLp f 2).toLp f)
      ((hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2).toLp g)≤
    C*dist ((compact_C1_gradient_memLp hf hc).toLp (gradient f))
      ((compact_C1_gradient_memLp hg hgc).toLp (gradient g)) := by
  have hp := hP (f-g) (hf.sub hg) (hc.sub hgc)
    ((tsupport_sub f g).trans (union_subset hs hgs))
  rw [Lp.norm_toLp,Lp.norm_toLp,C1_gradient_sub hf hg] at hp
  simpa only [Lp.dist_edist,Lp.edist_toLp_toLp] using hp

lemma cauchySeq_of_distance_comparison {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℕ → X} {g : ℕ → Y} {C : ℝ} (hC : 0≤C)
    (hg : CauchySeq g) (hbound : ∀ i j,dist (f i) (f j)≤C*dist (g i) (g j)) :
    CauchySeq f := by
  rw [Metric.cauchySeq_iff] at hg ⊢
  intro ε hε
  have hCp : 0<C+1 := by linarith
  obtain ⟨N,hN⟩ := hg (ε/(C+1)) (div_pos hε hCp)
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  calc
    dist (f i) (f j) ≤ C*dist (g i) (g j) := hbound i j
    _ ≤ (C+1)*dist (g i) (g j) := by nlinarith [(dist_nonneg : 0≤dist (g i) (g j))]
    _ < ε := (lt_div_iff₀' hCp).mp (hN i hi j hj)

theorem zeroBoundaryGradientSpace_primitive {R : ℝ}
    {G : Lp Plane 2 (volume : Measure Plane)}
    (hG : G∈zeroBoundaryGradientSpace (Metric.ball 0 R)) :
    ∃ u : Lp ℝ 2 (volume : Measure Plane), PlaneWeakGradient univ u G ∧
      ∃ f : ℕ → Plane → ℝ, ∃ hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i),
        ∃ hc : ∀ i,HasCompactSupport (f i), (∀ i,tsupport (f i)⊆Metric.ball 0 R) ∧
        Tendsto (fun i ↦ ((hf i).continuous.memLp_of_hasCompactSupport (hc i) :
          MemLp (f i) 2 volume).toLp (f i)) atTop (𝓝 u) ∧
        Tendsto (fun i ↦ (compact_C1_gradient_memLp ((hf i).of_le (by simp)) (hc i)).toLp
          (gradient (f i))) atTop (𝓝 G) := by
  obtain ⟨C,hC,hP⟩ := compact_test_poincare R
  obtain ⟨f,hf,hc,hs,hlim⟩ := zeroBoundaryGradientSpace_approximation hG
  let U (i : ℕ) : Lp ℝ 2 (volume : Measure Plane) :=
    ((hf i).continuous.memLp_of_hasCompactSupport (hc i) : MemLp (f i) 2 volume).toLp (f i)
  let F (i : ℕ) : Lp Plane 2 (volume : Measure Plane) :=
    (compact_C1_gradient_memLp ((hf i).of_le (by simp)) (hc i)).toLp (gradient (f i))
  have hbound (i j : ℕ) : dist (U i) (U j)≤C*dist (F i) (F j) :=
    compact_test_poincare_difference hP ((hf i).of_le (by simp)) ((hf j).of_le (by simp))
      (hc i) (hc j) (hs i) (hs j)
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_distance_comparison hC hlim.cauchySeq hbound)
  refine ⟨u,?_,f,hf,hc,hs,hu,hlim⟩
  apply PlaneWeakGradient.L2_limit hu hlim
  intro i
  apply (compact_C1_weak_gradient ((hf i).of_le (by simp)) (hc i) univ).congr
  · exact ((hf i).continuous.memLp_of_hasCompactSupport (hc i) : MemLp (f i) 2 volume).coeFn_toLp
  · exact (compact_C1_gradient_memLp ((hf i).of_le (by simp)) (hc i)).coeFn_toLp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem plane_harmonic_replacement (R : ℝ)
    (G : Lp Plane 2 (volume : Measure Plane)) :
    ∃ W : Lp Plane 2 (volume : Measure Plane),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 R) ∧
      ‖W‖≤‖G‖ ∧
      (∀ F∈zeroBoundaryGradientSpace (Metric.ball 0 R), ⟪G-W,F⟫=0) ∧
      ∃ w : Lp ℝ 2 (volume : Measure Plane), PlaneWeakGradient univ w W := by
  let K := zeroBoundaryGradientSpace (Metric.ball (0 : Plane) R)
  let : IsClosed (K : Set (Lp Plane 2 (volume : Measure Plane))) :=
    zeroBoundaryGradientSpace_isClosed _
  let W := K.starProjection G
  have hW : W∈K := K.starProjection_apply_mem G
  obtain ⟨w,hw,_⟩ := zeroBoundaryGradientSpace_primitive hW
  exact ⟨W,hW,K.norm_starProjection_apply_le G,
    fun F hF ↦ K.starProjection_inner_eq_zero G F hF,w,hw⟩

lemma L2_pair_gradient_test {G : Lp Plane 2 (volume : Measure Plane)}
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    ⟪G,(compact_C1_gradient_memLp hψ hc).toLp (gradient ψ)⟫=
      ∫ y, fderiv ℝ ψ y (G y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compact_C1_gradient_memLp hψ hc).coeFn_toLp] with y hy
  simp only [hy,inner_gradient_right,conj_trivial]

lemma harmonic_replacement_test {R : ℝ} {G W : Lp Plane 2 (volume : Measure Plane)}
    (ho : ∀ F∈zeroBoundaryGradientSpace (Metric.ball 0 R), ⟪G-W,F⟫=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    (∫ y, fderiv ℝ ψ y ((G-W) y))=0 := by
  rw [← L2_pair_gradient_test (hψ.of_le (by simp)) hc]
  apply ho
  exact (smoothGradientSpace (Metric.ball 0 R)).le_topologicalClosure
    ⟨ψ,hψ,hc,hs,rfl⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma L2_scalar_test_integrable (u : Lp ℝ 2 (volume : Measure Plane))
    {ψ : Plane → ℝ} (hψ : MemLp ψ 2 volume) : Integrable (fun y ↦ u y*ψ y) := by
  apply (L2.integrable_inner (𝕜 := ℝ) u (hψ.toLp ψ)).congr
  filter_upwards [hψ.coeFn_toLp] with y hy
  simp only [hy,RCLike.inner_apply,conj_trivial]
  ring

lemma L2_vector_test_integrable (G : Lp Plane 2 (volume : Measure Plane))
    {F : Plane → Plane} (hF : MemLp F 2 volume) : Integrable (fun y ↦ ⟪G y,F y⟫) := by
  apply (L2.integrable_inner (𝕜 := ℝ) G (hF.toLp F)).congr
  filter_upwards [hF.coeFn_toLp] with y hy
  exact congrArg (inner ℝ (G y)) hy

lemma PlaneWeakGradient.Lp_sub {S : Set Plane}
    {u w : Lp ℝ 2 (volume : Measure Plane)} {G W : Lp Plane 2 (volume : Measure Plane)}
    (hu : PlaneWeakGradient S u G) (hw : PlaneWeakGradient S w W) :
    PlaneWeakGradient S ((u-w : Lp ℝ 2 volume) : Plane → ℝ)
      ((G-W : Lp Plane 2 volume) : Plane → Plane) := by
  intro v ψ hψ hc hs
  let a : Plane → Plane := fun y ↦ ψ y • v
  have ha : MemLp a 2 volume := (hψ.continuous.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right
  let A := ha.toLp a
  let b : Plane → ℝ := fun y ↦ fderiv ℝ ψ y v
  have hb : MemLp b 2 volume := ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hc.fderiv_apply ℝ v)
  let B := hb.toLp b
  have h₁ : ⟪G,A⟫= -⟪u,B⟫ := by
    rw [L2_pair_vector_test hψ.continuous hc v,L2_pair_scalar_test hb]
    exact hu v ψ hψ hc hs
  have h₂ : ⟪W,A⟫= -⟪w,B⟫ := by
    rw [L2_pair_vector_test hψ.continuous hc v,L2_pair_scalar_test hb]
    exact hw v ψ hψ hc hs
  rw [← L2_pair_vector_test hψ.continuous hc v,← L2_pair_scalar_test hb]
  change ⟪G-W,A⟫= -⟪u-w,B⟫
  rw [inner_sub_left,inner_sub_left,h₁,h₂]
  ring

end CubicTorus
end
end
end

end OAI
