import Mathlib
import OAI.Geometry.CubicTorus.Curvature.LinearCMCEquation

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.local_gradient_energy {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    {M : ℝ} (hBb : ∀ y,‖B y‖≤M) {R r s : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hs : 0<s) (hsr : s<r)
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) :
    ∃ C : ℝ,0≤C ∧ ∀ a : Plane,r+‖a‖≤R →
      (∫ y in Metric.ball 0 s,‖gradient g (y+a)-gradient g y‖^2)≤C*‖a‖^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨s,(s+r)/2,hs,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hi := compact_derivative_square_integrable (b.contDiff (n := 1)) b.hasCompactSupport
  have hb2 : Integrable (fun y ↦ b y^2) := by
    have hbc : Continuous (fun y : Plane ↦ b y * b y) := b.continuous.mul b.continuous
    have hbsq : HasCompactSupport (fun y : Plane ↦ b y * b y) := b.hasCompactSupport.mul_right
    have hi : Integrable (fun y : Plane ↦ b y * b y) (volume : Measure Plane) := hbc.integrable_of_hasCompactSupport hbsq
    exact hi.congr (Eventually.of_forall fun y ↦ by ring)
  let D : ℝ := (LB:ℝ)+(LA:ℝ)*(K:ℝ)
  let C : ℝ := 4096*(K:ℝ)^2*(∫ y,‖fderiv ℝ b y‖^2)+256*D^2*(∫ y,b y^2)
  have hC : 0≤C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ sq_nonneg _))
      (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ sq_nonneg _))
  refine ⟨C,hC,fun a ha ↦ ?_⟩
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg (b.contDiff (n := 1)) b.hasCompactSupport a
  have hbound : (∫ y,(g (y+a)-g y)^2*‖fderiv ℝ b y‖^2)≤
      ((K:ℝ)*‖a‖)^2*(∫ y,‖fderiv ℝ b y‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono hBi (hi.const_mul _)
    intro y
    have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖fderiv ℝ b y‖)]
  have hsource : (∫ y,b y^2*‖B (y+a)-B y-
      (cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)‖^2)≤
      (D*‖a‖)^2*(∫ y,b y^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity) (hb2.const_mul _)
    exact Eventually.of_forall fun y ↦ by
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (linear_cmc_difference_source_bound hg hA hB y a) 2) (sq_nonneg (b y))
      dsimp only [D]
      nlinarith
  calc
    (∫ y in Metric.ball 0 s,‖gradient g (y+a)-gradient g y‖^2) =
        ∫ y in Metric.ball 0 s,b y^2*‖gradient g (y+a)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      dsimp only
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
      simp
    _ ≤ ∫ y,b y^2*‖gradient g (y+a)-gradient g y‖^2 :=
      setIntegral_le_integral hAi (ae_of_all _ fun _ ↦ by positivity)
    _ ≤ 4096*(∫ y,(g (y+a)-g y)^2*‖fderiv ℝ b y‖^2)+256*(∫ y,b y^2*‖B (y+a)-B y-
        (cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)‖^2) :=
      hw.caccioppoli hg hp hpb hB.continuous hBb hgc (by linarith) ha b.contDiff b.hasCompactSupport hbs
    _ ≤ 4096*(((K:ℝ)*‖a‖)^2*(∫ y,‖fderiv ℝ b y‖^2))+256*((D*‖a‖)^2*(∫ y,b y^2)) := by linarith
    _ = C*‖a‖^2 := by dsimp only [C]; ring

end CubicTorus

end
end

section

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace CubicTorus
universe uHilbert

theorem hilbert_bounded_weak_subsequence {E : Type uHilbert}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (f : ℕ → E) {M : ℝ}
    (hb : ∀ i, ‖f i‖≤M) :
    ∃ (u : E) (φ : ℕ → ℕ), ‖u‖≤M ∧ StrictMono φ ∧
      ∀ v : E, Tendsto (fun i ↦ ⟪f (φ i),v⟫) atTop (𝓝 ⟪u,v⟫) := by
  let F : ℕ → WeakDual ℝ E := fun i ↦ StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ E) (f i))
  have hm (i : ℕ) : F i∈WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M := by
    simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right]
    change ‖(InnerProductSpace.toDual ℝ E) (f i)‖≤M
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    exact hb i
  obtain ⟨L,hL,φ,hφ,hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) M) hm
  let u : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L)
  refine ⟨u,φ,?_,hφ,fun v ↦ ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ E).symm _‖≤M
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hL
  · have hh := ((WeakDual.eval_continuous v).tendsto L).comp hlim
    simpa only [F,Function.comp_def,StrongDual.toWeakDual_apply,InnerProductSpace.toDual_apply_apply,
      u,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_difference_quotient_pairing {f ψ : Plane → ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (v : Plane) :
    (∫ y, (t⁻¹*(f (y+t • v)-f y))*ψ y)=
      ∫ y, (t⁻¹*(ψ (y+t • (-v))-ψ y))*f y := by
  have h₁ : Integrable (fun y ↦ f (y+t • v)*ψ y) :=
    ((hf.comp (continuous_id.add continuous_const)).mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have h₂ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have h₃ : Integrable (fun y ↦ f y*ψ (y+t • (-v))) :=
    (hf.mul (hψ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left
  have he : (∫ y, f (y+t • v)*ψ y)=(∫ y, f y*ψ (y+t • (-v))) := by
    rw [← integral_add_right_eq_self _ (t • (-v))]
    simp
  simp_rw [mul_assoc,← mul_comm (f _),sub_mul,mul_sub]
  rw [integral_sub (h₁.const_mul _) (h₂.const_mul _),
    integral_sub (h₃.const_mul _) (h₂.const_mul _),integral_const_mul,integral_const_mul,
    integral_const_mul,he]

theorem continuous_difference_quotient_test_limit {f ψ : Plane → ℝ}
    (hf : Continuous f) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (v : Plane) :
    Tendsto (fun t : ℝ ↦ ∫ y, (t⁻¹*(f (y+t • v)-f y))*ψ y) (𝓝[>] 0)
      (𝓝 (-(∫ y, f y*fderiv ℝ ψ y v))) := by
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hh := LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (μ := (volume : Measure Plane)) hL hc hf (-v)
  have he : (∫ y, lineDeriv ℝ ψ y (-v)*f y)= -(∫ y, f y*fderiv ℝ ψ y v) := by
    simp_rw [(hψ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
      map_neg,neg_mul,integral_neg,mul_comm _ (f _)]
  rw [he] at hh
  convert hh using 1
  funext t
  exact continuous_difference_quotient_pairing hf hψ.continuous hc t v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem continuous_L2_weak_directional_derivative {f : Plane → ℝ}
    (hf : Continuous f) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    {r δ C : ℝ} (hδ : 0<δ) (hC : 0≤C) (v : Plane)
    (he : ∀ t∈Ioc 0 δ, (∫ y in Metric.ball 0 r, (f (y+t • v)-f y)^2)≤C*t^2) :
    ∃ u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) r)), ‖u‖≤Real.sqrt C ∧
      ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ⊆Metric.ball 0 r →
        (∫ y in Metric.ball 0 r, u y*ψ y)= -(∫ y, f y*fderiv ℝ ψ y v) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : Fact ((2 : ℝ≥0∞)≠⊤) := ⟨by norm_num⟩
  let t : ℕ → ℝ := fun i ↦ δ*(1/((i:ℝ)+1))
  have ht (i : ℕ) : t i∈Ioc 0 δ := by
    have hn : (1:ℝ)≤(i:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    constructor
    · dsimp only [t]; positivity
    · dsimp only [t]
      exact mul_le_of_le_one_right hδ.le (by rw [div_le_one (by linarith : (0:ℝ)<(i:ℝ)+1)]; exact hn)
  have htlim : Tendsto t atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall (fun i ↦ (ht i).1)⟩
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  let q : ℕ → Plane → ℝ := fun i y ↦ (t i)⁻¹*(f (y+t i • v)-f y)
  have hqm (i : ℕ) : MemLp (q i) 2 μ := by
    apply MemLp.of_bound (C := |(t i)⁻¹| *(2*M)) (by fun_prop)
    filter_upwards [] with y
    change ‖(t i)⁻¹*(f (y+t i • v)-f y)‖≤_
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hb (y+t i • v),hb y]))
      (abs_nonneg _)
  let Q : ℕ → Lp ℝ 2 μ := fun i ↦ (hqm i).toLp (q i)
  have hQ (i : ℕ) : ‖Q i‖≤Real.sqrt C := by
    have heq : ‖Q i‖^2=(t i)⁻¹^2*(∫ y in Metric.ball 0 r, (f (y+t i • v)-f y)^2) := by
      rw [L2_norm_sq_integral]
      calc
        _ = ∫ y, (q i y)^2 ∂μ := integral_congr_ae ((hqm i).coeFn_toLp.mono (fun y hy ↦ by rw [hy]))
        _ = _ := by simp only [q,mul_pow,integral_const_mul,μ]
    have hh := mul_le_mul_of_nonneg_left (he (t i) (ht i)) (sq_nonneg (t i)⁻¹)
    have htne := (ht i).1.ne'
    have hsq := Real.sq_sqrt hC
    have hre : (t i)⁻¹^2*(C*(t i)^2)=C := by field_simp
    rw [hre,← heq] at hh
    nlinarith [norm_nonneg (Q i),Real.sqrt_nonneg C]
  obtain ⟨u,φ,hu,hφ,hlim⟩ := hilbert_bounded_weak_subsequence Q hQ
  refine ⟨u,hu,fun ψ hψ hc hs ↦ ?_⟩
  have hψm : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hc
  let V : Lp ℝ 2 μ := hψm.toLp ψ
  have hpair (i : ℕ) : ⟪Q i,V⟫=(∫ y, q i y*ψ y) := by
    rw [L2.inner_def,integral_mul_eq_restrict_of_tsupport measurableSet_ball (q i) ψ hs]
    apply integral_congr_ae
    filter_upwards [(hqm i).coeFn_toLp,hψm.coeFn_toLp] with y hy hψy
    simp only [RCLike.inner_apply,RCLike.conj_to_real]
    rw [hy,hψy]
    ring
  have hupair : ⟪u,V⟫=(∫ y in Metric.ball 0 r, u y*ψ y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψm.coeFn_toLp] with y hy
    simp only [RCLike.inner_apply,RCLike.conj_to_real]
    rw [hy]
    ring
  have hlim₁ := (hlim V)
  simp only [hpair,hupair] at hlim₁
  have hlim₂ := (continuous_difference_quotient_test_limit hf hψ hc v).comp
    (htlim.comp hφ.tendsto_atTop)
  exact tendsto_nhds_unique hlim₁ hlim₂

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_cutoff {f η : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hη : Continuous η)
    (hs : tsupport η⊆U) : Continuous (fun y ↦ η y*f y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.continuousAt.mul ((hf y (hs hy)).continuousAt (hU.mem_nhds (hs hy)))
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma C1_gradient_continuousOn {g : Plane → ℝ} {U : Set Plane}
    (hg : ContDiffOn ℝ 1 g U) (hU : IsOpen U) : ContinuousOn (gradient g) U :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    (hg.continuousOn_fderiv_of_isOpen hU le_rfl)

theorem WeakCMCGraph.weak_hessian {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) (v w : Plane) (hv : ‖v‖≤1) (hw' : ‖w‖≤1) :
    ∃ u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), u y*ψ y)=
          -(∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v) := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f : Plane → ℝ := fun y ↦ b y*⟪gradient g y,w⟫
  have hfc : Continuous f := continuous_local_cutoff Metric.isOpen_ball
    ((C1_gradient_continuousOn hgc Metric.isOpen_ball).inner continuousOn_const) b.continuous hbs
  have hgrad (y : Plane) : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hfb (y : Plane) : ‖f y‖≤(K:ℝ) := by
    dsimp only [f]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (b.nonneg (x := y))]
    have hi : ‖⟪gradient g y,w⟫‖≤(K:ℝ) := (norm_inner_le_norm _ _).trans
      (by nlinarith [hgrad y,norm_nonneg (gradient g y),norm_nonneg w,K.coe_nonneg])
    exact (mul_le_mul_of_nonneg_left hi (b.nonneg (x := y))).trans
      (mul_le_of_le_one_left K.coe_nonneg (b.le_one (x := y)))
  have hfeq {y : Plane} (hy : ‖y‖≤R/2) : f y=⟪gradient g y,w⟫ := by
    dsimp only [f]
    rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy),one_mul]
  obtain ⟨C,hC,henergy⟩ := hw.local_gradient_energy hg hK hgc
    (show 0<R/4 by linarith) (show R/4<R/2 by linarith)
  have he : ∀ t∈Ioc 0 (R/4), (∫ y in Metric.ball 0 (R/4), (f (y+t • v)-f y)^2)≤C*t^2 := by
    intro t ht
    have ha : ‖t • v‖≤t := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
      exact mul_le_of_le_one_right ht.1.le hv
    have haR : R/2+‖t • v‖≤R := by linarith [ht.2]
    have hfc' : Continuous (fun y ↦ (f (y+t • v)-f y)^2) :=
      ((hfc.comp (continuous_id.add continuous_const)).sub hfc).pow 2
    have hfi : IntegrableOn (fun y ↦ (f (y+t • v)-f y)^2) (Metric.ball 0 (R/4)) := hfc'.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) (R/4))
      |>.mono_set Metric.ball_subset_closedBall
    have hgm := measurable_plane_gradient g
    have hgi : IntegrableOn (fun y ↦ ‖gradient g (y+t • v)-gradient g y‖^2) (Metric.ball 0 (R/4)) := by
      apply (integrableOn_const (C := (2*(K:ℝ))^2) measure_ball_lt_top.ne).mono'
        (((hgm.comp (measurable_id.add_const _)).sub hgm).norm.pow_const 2).aestronglyMeasurable
      filter_upwards [] with y
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (gradient_difference_norm_le hg y (t • v)) 2
    calc
      _ ≤ ∫ y in Metric.ball 0 (R/4), ‖gradient g (y+t • v)-gradient g y‖^2 := by
        apply integral_mono_ae hfi hgi
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        have hy' : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
        rw [hfeq ((norm_add_le y (t • v)).trans (by linarith [ht.2])),hfeq (by linarith),← inner_sub_left]
        have hi := (norm_inner_le_norm (𝕜 := ℝ) (gradient g (y+t • v)-gradient g y) w).trans
          (mul_le_of_le_one_right (norm_nonneg _) hw')
        simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hi 2
      _ ≤ C*‖t • v‖^2 := henergy (t • v) haR
      _ ≤ C*t^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2) hC
  obtain ⟨u,_hu,hud⟩ := continuous_L2_weak_directional_derivative hfc hfb
    (show 0<R/4 by linarith) hC v he
  refine ⟨u,fun ψ hψ hc hs ↦ ?_⟩
  rw [hud ψ hψ hc hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈tsupport ψ
  · rw [hfeq (by
      have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hs hy
      linarith)]
  · rw [fderiv_of_notMem_tsupport ℝ hy,zero_apply,mul_zero,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def differenceStep (δ : ℝ) (i : ℕ) : ℝ := δ*(1/((i:ℝ)+1))
def vectorDifference (f : Plane → Plane) (v : Plane) (t : ℝ) (y : Plane) : Plane :=
  t⁻¹ • (f (y+t • v)-f y)

lemma differenceStep_mem {δ : ℝ} (hδ : 0<δ) (i : ℕ) : differenceStep δ i∈Ioc 0 δ := by
  have hn : (1:ℝ)≤(i:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
  constructor
  · dsimp only [differenceStep]; positivity
  · dsimp only [differenceStep]
    exact mul_le_of_le_one_right hδ.le (by rw [div_le_one (by linarith : (0:ℝ)<(i:ℝ)+1)]; exact hn)

lemma differenceStep_tendsto {δ : ℝ} (hδ : 0<δ) : Tendsto (differenceStep δ) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,Eventually.of_forall (fun i ↦ (differenceStep_mem hδ i).1)⟩
  change Tendsto (fun i : ℕ ↦ δ*(1/((i:ℝ)+1))) atTop (𝓝 0)
  simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

lemma L2_vector_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Lp Plane 2 μ) : ‖u‖^2=∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma vectorDifference_memLp {f : Plane → Plane} (hf : Continuous f)
    {M : ℝ} (hb : ∀ y, ‖f y‖≤M) (r t : ℝ) (v : Plane) :
    MemLp (vectorDifference f v t) 2 (volume.restrict (Metric.ball 0 r)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Plane) r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply MemLp.of_bound (C := |t⁻¹| *(2*M)) (by unfold vectorDifference; fun_prop)
  filter_upwards [] with y
  rw [vectorDifference,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hb (y+t • v),hb y]))
    (abs_nonneg _)

theorem vector_L2_difference_subsequence {f : Plane → Plane}
    (hf : Continuous f) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    {r δ C : ℝ} (hδ : 0<δ) (hC : 0≤C) (v : Plane)
    (he : ∀ t∈Ioc 0 δ, (∫ y in Metric.ball 0 r, ‖f (y+t • v)-f y‖^2)≤C*t^2) :
    ∃ (u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))) (φ : ℕ → ℕ),
      ‖u‖≤Real.sqrt C ∧ StrictMono φ ∧
      ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
        Tendsto (fun i ↦ ⟪(vectorDifference_memLp hf hb r (differenceStep δ (φ i)) v).toLp
          (vectorDifference f v (differenceStep δ (φ i))),V⟫) atTop (𝓝 ⟪u,V⟫) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : Fact ((2 : ℝ≥0∞)≠⊤) := ⟨by norm_num⟩
  let Q : ℕ → Lp Plane 2 μ := fun i ↦ (vectorDifference_memLp hf hb r (differenceStep δ i) v).toLp
    (vectorDifference f v (differenceStep δ i))
  have hQ (i : ℕ) : ‖Q i‖≤Real.sqrt C := by
    have heq : ‖Q i‖^2=(differenceStep δ i)⁻¹^2*
        (∫ y in Metric.ball 0 r, ‖f (y+differenceStep δ i • v)-f y‖^2) := by
      rw [L2_vector_norm_sq_integral]
      calc
        _ = ∫ y, ‖vectorDifference f v (differenceStep δ i) y‖^2 ∂μ := integral_congr_ae
          ((vectorDifference_memLp hf hb r (differenceStep δ i) v).coeFn_toLp.mono (fun y hy ↦ by rw [hy]))
        _ = _ := by simp only [vectorDifference,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul,μ]
    have hh := mul_le_mul_of_nonneg_left (he _ (differenceStep_mem hδ i)) (sq_nonneg (differenceStep δ i)⁻¹)
    have htne := (differenceStep_mem hδ i).1.ne'
    have hsq := Real.sq_sqrt hC
    have hre : (differenceStep δ i)⁻¹^2*(C*(differenceStep δ i)^2)=C := by field_simp
    rw [hre,← heq] at hh
    nlinarith [norm_nonneg (Q i),Real.sqrt_nonneg C]
  exact hilbert_bounded_weak_subsequence Q hQ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_vector_cutoff {f : Plane → Plane} {η : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hη : Continuous η)
    (hs : tsupport η⊆U) : Continuous (fun y ↦ η y • f y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.continuousAt.smul ((hf y (hs hy)).continuousAt (hU.mem_nhds (hs hy)))
  · apply (continuousAt_const (y := (0:Plane))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

theorem WeakCMCGraph.gradient_difference_data {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R : ℝ} (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ (G : Plane → Plane) (C : ℝ), Continuous G ∧ (∀ y, ‖G y‖≤1) ∧ 0≤C ∧
      (∀ y, ‖y‖≤R/2 → G y=gradient g y) ∧
      ∀ v : Plane, ‖v‖≤1 → ∀ t∈Ioc 0 (R/4),
        (∫ y in Metric.ball 0 (R/4), ‖G (y+t • v)-G y‖^2)≤C*t^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let G : Plane → Plane := fun y ↦ b y • gradient g y
  have hGc : Continuous G := continuous_local_vector_cutoff Metric.isOpen_ball
    (C1_gradient_continuousOn hgc Metric.isOpen_ball) b.continuous hbs
  have hgrad (y : Plane) : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hGb (y : Plane) : ‖G y‖≤1 := by
    dsimp only [G]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
    exact ((mul_le_mul_of_nonneg_left (hgrad y) b.nonneg).trans
      (mul_le_of_le_one_left K.coe_nonneg b.le_one)).trans hK
  have hGeq {y : Plane} (hy : ‖y‖≤R/2) : G y=gradient g y := by
    dsimp only [G]
    rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy),one_smul]
  obtain ⟨C,hC,henergy⟩ := hw.local_gradient_energy hg hK hgc
    (show 0<R/4 by linarith) (show R/4<R/2 by linarith)
  refine ⟨G,C,hGc,hGb,hC,fun _ hy ↦ hGeq hy,fun v hv t ht ↦ ?_⟩
  have ha : ‖t • v‖≤t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact mul_le_of_le_one_right ht.1.le hv
  calc
    _ = ∫ y in Metric.ball 0 (R/4), ‖gradient g (y+t • v)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      have hy' : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      dsimp only
      rw [hGeq ((norm_add_le y (t • v)).trans (by linarith [ht.2])),hGeq (by linarith)]
    _ ≤ C*‖t • v‖^2 := henergy (t • v) (by linarith [ht.2])
    _ ≤ C*t^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2) hC

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.gradient_difference_data {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) :
    ∃ (G : Plane → Plane) (C : ℝ), Continuous G ∧ (∀ y, ‖G y‖≤(K:ℝ)) ∧ 0≤C ∧
      (∀ y, ‖y‖≤R/2 → G y=gradient g y) ∧
      ∀ v : Plane, ‖v‖≤1 → ∀ t∈Ioc 0 (R/4),
        (∫ y in Metric.ball 0 (R/4), ‖G (y+t • v)-G y‖^2)≤C*t^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let G : Plane → Plane := fun y ↦ b y • gradient g y
  have hGc : Continuous G := continuous_local_vector_cutoff Metric.isOpen_ball
    (C1_gradient_continuousOn hgc Metric.isOpen_ball) b.continuous hbs
  have hgrad (y : Plane) : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hGb (y : Plane) : ‖G y‖≤(K:ℝ) := by
    dsimp only [G]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
    exact (mul_le_mul_of_nonneg_left (hgrad y) b.nonneg).trans
      (mul_le_of_le_one_left K.coe_nonneg b.le_one)
  have hGeq {y : Plane} (hy : ‖y‖≤R/2) : G y=gradient g y := by
    dsimp only [G]
    rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy),one_smul]
  obtain ⟨C,hC,henergy⟩ := hw.local_gradient_energy hg hp hpb hA hB hBb hgc
    (show 0<R/4 by linarith) (show R/4<R/2 by linarith)
  refine ⟨G,C,hGc,hGb,hC,fun _ hy ↦ hGeq hy,fun v hv t ht ↦ ?_⟩
  have ha : ‖t • v‖≤t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact mul_le_of_le_one_right ht.1.le hv
  calc
    _ = ∫ y in Metric.ball 0 (R/4), ‖gradient g (y+t • v)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      have hy' : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      dsimp only
      rw [hGeq ((norm_add_le y (t • v)).trans (by linarith [ht.2])),hGeq (by linarith)]
    _ ≤ C*‖t • v‖^2 := henergy (t • v) (by linarith [ht.2])
    _ ≤ C*t^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2) hC

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_vector_quotient_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} {K : ℝ≥0} (hf : LipschitzWith K f) {t : ℝ} (ht : t≠0) (y v : Plane) :
    ‖t⁻¹ • (f (y+t • v)-f y)‖≤(K:ℝ)*‖v‖ := by
  have hh : ‖f (y+t • v)-f y‖≤(K:ℝ)*(|t| *‖v‖) := by
    simpa only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] using hf.dist_le_mul (y+t • v) y
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |t|⁻¹*((K:ℝ)*(|t| *‖v‖)) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by field_simp

lemma differentiable_vector_quotient_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} {y : Plane} (hf : DifferentiableAt ℝ f y) (v : Plane)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[>] 0)) :
    Tendsto (fun i ↦ (t i)⁻¹ • (f (y+t i • v)-f y)) atTop (𝓝 (fderiv ℝ f y v)) :=
  (hf.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right.comp ht

lemma linear_source_difference_limit {f : Plane → Plane} (hf : Continuous f)
    {M : ℝ} (hb : ∀ y,‖f y‖≤M) {A : Plane → Plane →L[ℝ] Plane} {B : Plane → Plane}
    {LA LB : ℝ≥0} (hA : LipschitzWith LA A) (hB : LipschitzWith LB B)
    (hAd : Differentiable ℝ A) (hBd : Differentiable ℝ B)
    {r : ℝ} {t : ℕ → ℝ} (ht : ∀ i,0<t i) (htlim : Tendsto t atTop (𝓝[>] 0))
    (v : Plane) {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,fderiv ℝ ψ y
      (((t i)⁻¹ • (A (y+t i • v)-A y)) (f (y+t i • v))-(t i)⁻¹ • (B (y+t i • v)-B y))) atTop
      (𝓝 (∫ y in Metric.ball 0 r,fderiv ℝ ψ y (fderiv ℝ A y v (f y)-fderiv ℝ B y v))) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (L:ℝ)*((LA:ℝ)*‖v‖*M+(LB:ℝ)*‖v‖))
  · intro i
    apply Continuous.aestronglyMeasurable
    have hcA : Continuous (fun y : Plane ↦ (t i)⁻¹ • (A (y+t i • v)-A y)) :=
      ((hA.continuous.comp (continuous_id.add continuous_const)).sub hA.continuous).const_smul ((t i)⁻¹ : ℝ)
    have hcB : Continuous (fun y : Plane ↦ (t i)⁻¹ • (B (y+t i • v)-B y)) :=
      ((hB.continuous.comp (continuous_id.add continuous_const)).sub hB.continuous).const_smul ((t i)⁻¹ : ℝ)
    exact (hψ.continuous_fderiv (by simp)).clm_apply
      ((hcA.clm_apply (hf.comp (continuous_id.add continuous_const))).sub hcB)
  · exact integrable_const _
  · intro i
    exact Eventually.of_forall fun y ↦ by
      have h₁ := (ContinuousLinearMap.le_opNorm ((t i)⁻¹ • (A (y+t i • v)-A y)) (f (y+t i • v))).trans
        (mul_le_mul (lipschitz_vector_quotient_bound hA (ht i).ne' y v) (hb _) (norm_nonneg _) (by positivity))
      have h₂ := lipschitz_vector_quotient_bound hB (ht i).ne' y v
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
        (norm_fderiv_le_of_lipschitz ℝ hL) ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) (norm_nonneg _) L.coe_nonneg)
  · exact Eventually.of_forall fun y ↦ by
      have hy : Tendsto (fun i ↦ y+t i • v) atTop (𝓝 y) := by
        simpa only [zero_smul,add_zero] using
          (tendsto_const_nhds (x := y)).add ((tendsto_nhds_of_tendsto_nhdsWithin htlim).smul (tendsto_const_nhds (x := v)))
      apply (fderiv ℝ ψ y).continuous.tendsto _ |>.comp
      have heval : Continuous (fun z : (Plane →L[ℝ] Plane) × Plane ↦ z.1 z.2) :=
        continuous_fst.clm_apply continuous_snd
      exact ((heval.tendsto _).comp ((differentiable_vector_quotient_limit (hAd y) v htlim).prodMk_nhds
        (hf.continuousAt.tendsto.comp hy))).sub (differentiable_vector_quotient_limit (hBd y) v htlim)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem vector_weak_quotient_derivative {f : Plane → Plane} (hf : Continuous f)
    {r : ℝ} {t : ℕ → ℝ} (htlim : Tendsto t atTop (𝓝[>] 0)) (v w : Plane)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i, (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y in Metric.ball 0 r, ⟪u y,w⟫*ψ y)= -(∫ y, ⟪f y,w⟫*fderiv ℝ ψ y v) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let W : Plane → Plane := fun y ↦ ψ y • w
  have hWc : Continuous W := hψ.continuous.smul continuous_const
  have hWs : HasCompactSupport W := hc.smul_right
  have hWm : MemLp W 2 μ := hWc.memLp_of_hasCompactSupport hWs
  let V : Lp Plane 2 μ := hWm.toLp W
  have hp (i : ℕ) : ⟪Q i,V⟫=(∫ y, ((t i)⁻¹*(⟪f (y+t i • v),w⟫-⟪f y,w⟫))*ψ y) := by
    rw [L2.inner_def,integral_mul_eq_restrict_of_tsupport measurableSet_ball _ ψ hs]
    apply integral_congr_ae
    filter_upwards [hQ i,hWm.coeFn_toLp] with y hy hy'
    rw [hy,hy']
    simp only [W,vectorDifference,inner_smul_right,inner_smul_left,inner_sub_left,RCLike.conj_to_real]
    ring
  have hup : ⟪u,V⟫=(∫ y in Metric.ball 0 r, ⟪u y,w⟫*ψ y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWm.coeFn_toLp] with y hy
    rw [hy]
    simp only [W,inner_smul_right]
    ring
  have hlim₁ := hw V
  simp_rw [hp,hup] at hlim₁
  have hlim₂ := (continuous_difference_quotient_test_limit (hf.inner (continuous_const (y := w))) hψ hc v).comp htlim
  exact tendsto_nhds_unique hlim₁ hlim₂

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma weak_linear_cmc_pairing {f : Plane → Plane} {p : Plane → Plane}
    (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1) {r : ℝ} {t : ℕ → ℝ} (v : Plane)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i,(Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,fderiv ℝ ψ y (cmcJacobian (p y) (vectorDifference f v (t i) y))) atTop
      (𝓝 (∫ y in Metric.ball 0 r,fderiv ℝ ψ y (cmcJacobian (p y) (u y)))) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hgrad (y : Plane) : ‖gradient ψ y‖≤(L:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL
  let W : Plane → Plane := fun y ↦ cmcJacobian (p y) (gradient ψ y)
  have hWcont : Continuous W := (cmcJacobian_contDiff.continuous.comp hp).clm_apply
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ.continuous_fderiv (by simp)))
  have hWb (y : Plane) : ‖W y‖≤2*(L:ℝ) :=
    (cmcJacobian_norm_le (hpb y) _).trans (by gcongr; exact hgrad y)
  have hW : MemLp W 2 μ := MemLp.of_bound hWcont.aestronglyMeasurable (C := 2*(L:ℝ)) (Eventually.of_forall hWb)
  let V : Lp Plane 2 μ := hW.toLp W
  have hid (y z : Plane) : ⟪z,W y⟫=fderiv ℝ ψ y (cmcJacobian (p y) z) := by
    dsimp only [W]
    rw [cmcJacobian_symmetric,real_inner_comm,inner_gradient_left]
  have hpair (i : ℕ) : ⟪Q i,V⟫=(∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (vectorDifference f v (t i) y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ i,hW.coeFn_toLp] with y hy hz
    rw [hy,hz,hid]
  have hup : ⟪u,V⟫=(∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (u y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with y hy
    rw [hy,hid]
  have hh := hw V
  simpa only [hpair,hup,μ] using hh

lemma Lp.cmc_differential_integrable {p : Plane → Plane}
    (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1) (r : ℝ)
    (u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun y ↦ fderiv ℝ ψ y (cmcJacobian (p y) (u y)))
      (volume.restrict (Metric.ball (0 : Plane) r)) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  let W : Plane → Plane := fun y ↦ cmcJacobian (p y) (gradient ψ y)
  have hWc : Continuous W := (cmcJacobian_contDiff.continuous.comp hp).clm_apply
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ.continuous_fderiv (by simp)))
  have hWb (y : Plane) : ‖W y‖≤2*(L:ℝ) := by
    have hg : ‖gradient ψ y‖≤(L:ℝ) := by
      rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL
    exact (cmcJacobian_norm_le (hpb y) _).trans (by linarith)
  have hW : MemLp W 2 μ := MemLp.of_bound hWc.aestronglyMeasurable (C := 2*(L:ℝ)) (Eventually.of_forall hWb)
  apply (L2.integrable_inner (𝕜 := ℝ) u (hW.toLp W)).congr
  filter_upwards [hW.coeFn_toLp] with y hy
  rw [hy]
  dsimp only [W]
  rw [cmcJacobian_symmetric,real_inner_comm,inner_gradient_left]

theorem weak_L2_linear_cmc_chain {f : Plane → Plane} (hf : Continuous f)
    {M : ℝ} (hb : ∀ y,‖f y‖≤M) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAd : Differentiable ℝ (fun y ↦ cmcJacobian (p y))) (hBd : Differentiable ℝ B)
    {r : ℝ} {t : ℕ → ℝ} (ht : ∀ i,0<t i) (htlim : Tendsto t atTop (𝓝[>] 0))
    (v : Plane) {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i,(Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,fderiv ℝ ψ y ((t i)⁻¹ •
      ((cmcJacobian (p (y+t i • v)) (f (y+t i • v))-B (y+t i • v))-
        (cmcJacobian (p y) (f y)-B y)))) atTop
      (𝓝 ((∫ y in Metric.ball 0 r,fderiv ℝ ψ y (cmcJacobian (p y) (u y)))+
        (∫ y in Metric.ball 0 r,fderiv ℝ ψ y
          (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (f y)-fderiv ℝ B y v)))) := by
  have h₁ := weak_linear_cmc_pairing hp hpb v hQ hw hψ hc
  have h₂ := linear_source_difference_limit hf hb hA hB hAd hBd ht htlim v hψ hc (r := r)
  convert h₁.add h₂ using 1
  funext i
  let A : Plane → Plane →L[ℝ] Plane := fun y ↦ cmcJacobian (p y)
  have hD : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hAi : Continuous (fun y : Plane ↦ A y (vectorDifference f v (t i) y)) :=
    hA.continuous.clm_apply (((hf.comp (continuous_id.add continuous_const)).sub hf).const_smul ((t i)⁻¹ : ℝ))
  have hSi : Continuous (fun y : Plane ↦ ((t i)⁻¹ • (A (y+t i • v)-A y)) (f (y+t i • v))-
      (t i)⁻¹ • (B (y+t i • v)-B y)) := by
    have hcA : Continuous (fun y : Plane ↦ (t i)⁻¹ • (A (y+t i • v)-A y)) :=
      ((hA.continuous.comp (continuous_id.add continuous_const)).sub hA.continuous).const_smul ((t i)⁻¹ : ℝ)
    have hcB : Continuous (fun y : Plane ↦ (t i)⁻¹ • (B (y+t i • v)-B y)) :=
      ((hB.continuous.comp (continuous_id.add continuous_const)).sub hB.continuous).const_smul ((t i)⁻¹ : ℝ)
    exact (hcA.clm_apply (hf.comp (continuous_id.add continuous_const))).sub hcB
  have hi₁ := (hD.clm_apply hAi).continuousOn.integrableOn_compact (μ := (volume : Measure Plane)) (isCompact_closedBall (0 : Plane) r)
    |>.mono_set Metric.ball_subset_closedBall
  have hi₂ := (hD.clm_apply hSi).continuousOn.integrableOn_compact (μ := (volume : Measure Plane)) (isCompact_closedBall (0 : Plane) r)
    |>.mono_set Metric.ball_subset_closedBall
  rw [← integral_add hi₁ hi₂]
  apply setIntegral_congr_fun measurableSet_ball
  intro y _hy
  dsimp only [A,vectorDifference]
  simp only [map_sub,map_smul,smul_eq_mul,sub_apply,smul_apply]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem weak_L2_cmc_chain {f : Plane → Plane} (hf : Continuous f)
    (hb : ∀ y, ‖f y‖≤1) {r C : ℝ} (hC : 0≤C) {t : ℕ → ℝ}
    (ht : ∀ i, 0<t i) (htlim : Tendsto t atTop (𝓝 0))
    (v : Plane)
    (henergy : ∀ i, (∫ y in Metric.ball 0 r, ‖f (y+t i • v)-f y‖^2)≤C*(t i)^2)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i, (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,
      fderiv ℝ ψ y ((t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)))) atTop
      (𝓝 (∫ y in Metric.ball 0 r, fderiv ℝ ψ y (cmcJacobian (f y) (u y)))) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  obtain ⟨B,hB,hrem⟩ := cmcFlux_quadratic_remainder
  have hgrad (y : Plane) : ‖gradient ψ y‖≤(L:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL
  let W : Plane → Plane := fun y ↦ cmcJacobian (f y) (gradient ψ y)
  have hWcont : Continuous W := (cmcJacobian_contDiff.continuous.comp hf).clm_apply
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ.continuous_fderiv (by simp)))
  have hWb (y : Plane) : ‖W y‖≤2*(L:ℝ) :=
    (cmcJacobian_norm_le (hb y) _).trans (by gcongr; exact hgrad y)
  have hW : MemLp W 2 μ := MemLp.of_bound hWcont.aestronglyMeasurable (C := 2*(L:ℝ)) (Eventually.of_forall hWb)
  let V : Lp Plane 2 μ := hW.toLp W
  have hid (y z : Plane) : ⟪z,W y⟫=fderiv ℝ ψ y (cmcJacobian (f y) z) := by
    dsimp only [W]
    rw [cmcJacobian_symmetric,real_inner_comm,inner_gradient_left]
  have hp (i : ℕ) : ⟪Q i,V⟫=(∫ y, fderiv ℝ ψ y (cmcJacobian (f y) (vectorDifference f v (t i) y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ i,hW.coeFn_toLp] with y hy hy'
    rw [hy,hy',hid]
  have hup : ⟪u,V⟫=(∫ y, fderiv ℝ ψ y (cmcJacobian (f y) (u y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with y hy
    rw [hy,hid]
  have hlim := hw V
  rw [hup] at hlim
  simp_rw [hp] at hlim
  let Err : ℕ → Plane → ℝ := fun i y ↦ fderiv ℝ ψ y ((t i)⁻¹ •
    (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)))
  have herr (i : ℕ) : ‖∫ y, Err i y ∂μ‖≤((L:ℝ)*B*C)*t i := by
    have hti : 0<(t i)⁻¹ := inv_pos.mpr (ht i)
    have hei : Integrable (fun y ↦ ‖f (y+t i • v)-f y‖^2) μ := by
      apply (integrable_const (4:ℝ)).mono' (by fun_prop)
      filter_upwards [] with y
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hh : ‖f (y+t i • v)-f y‖≤2 := (norm_sub_le _ _).trans (by linarith [hb (y+t i • v),hb y])
      nlinarith [norm_nonneg (f (y+t i • v)-f y)]
    calc
      _ ≤ ∫ y, ((L:ℝ)*B*(t i)⁻¹)*‖f (y+t i • v)-f y‖^2 ∂μ := by
        apply norm_integral_le_of_norm_le (hei.const_mul _)
        filter_upwards [] with y
        dsimp only [Err]
        calc
          _ ≤ (L:ℝ)*‖(t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y))‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
              (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
          _ = (L:ℝ)*((t i)⁻¹*‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖) := by
            rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (ht i))]
          _ ≤ (L:ℝ)*((t i)⁻¹*(B*‖f (y+t i • v)-f y‖^2)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (hrem _ _ (hb y) (hb (y+t i • v))) hti.le) L.coe_nonneg
          _ = _ := by ring
      _ = ((L:ℝ)*B*(t i)⁻¹)*(∫ y, ‖f (y+t i • v)-f y‖^2 ∂μ) := integral_const_mul _ _
      _ ≤ ((L:ℝ)*B*(t i)⁻¹)*(C*(t i)^2) := by
        simpa only [mul_comm] using mul_le_mul (henergy i)
          (le_refl ((L:ℝ)*B*(t i)⁻¹)) (by positivity) (mul_nonneg hC (sq_nonneg (t i)))
      _ = _ := by field_simp
  have herrlim : Tendsto (fun i ↦ ∫ y, Err i y ∂μ) atTop (𝓝 0) :=
    squeeze_zero_norm herr (by simpa using htlim.const_mul ((L:ℝ)*B*C))
  have hsum := hlim.add herrlim
  simp only [add_zero] at hsum
  convert hsum using 1
  funext i
  have hEi : Integrable (Err i) μ := by
    apply (integrable_const ((L:ℝ)*(t i)⁻¹*8)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      dsimp only [Err]
      have hD := hψ.continuous_fderiv (by simp)
      have hF := cmcFlux_contDiff.continuous
      have hJ := cmcJacobian_contDiff.continuous
      fun_prop
    · filter_upwards [] with y
      dsimp only [Err]
      have hrem8 : ‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖≤8 := by
        have hd : ‖f (y+t i • v)-f y‖≤2 := (norm_sub_le _ _).trans (by linarith [hb (y+t i • v),hb y])
        have h₁ := cmcFlux_difference_bound (hb y) (hb (y+t i • v))
        have h₂ := cmcJacobian_norm_le (hb y) (f (y+t i • v)-f y)
        exact (norm_sub_le _ _).trans (by linarith)
      calc
        _ ≤ (L:ℝ)*‖(t i)⁻¹ • (cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y))‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _))
        _ = (L:ℝ)*((t i)⁻¹*‖cmcFlux (f (y+t i • v))-cmcFlux (f y)-cmcJacobian (f y) (f (y+t i • v)-f y)‖) := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (ht i))]
        _ ≤ (L:ℝ)*((t i)⁻¹*8) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrem8 (inv_pos.mpr (ht i)).le) L.coe_nonneg
        _ = _ := by ring
  have hJi : Integrable (fun y ↦ fderiv ℝ ψ y (cmcJacobian (f y) (vectorDifference f v (t i) y))) μ := by
    have hi := L2.integrable_inner (𝕜 := ℝ) (Q i) V
    apply hi.congr
    filter_upwards [hQ i,hW.coeFn_toLp] with y hy hy'
    rw [hy,hy',hid]
  rw [← integral_add hJi hEi]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp only [Err,vectorDifference]
  simp only [map_sub,map_smul,smul_eq_mul]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
