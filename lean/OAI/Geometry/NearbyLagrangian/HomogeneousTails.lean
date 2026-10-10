import Mathlib
import OAI.Geometry.NearbyLagrangian.HamiltonianFlow
import OAI.Geometry.NearbyLagrangian.TameBounds

namespace OAI

/-! Uniform tame bounds for homogeneous tails and flat evolutions. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology InnerProductSpace
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma baseDifferential_homogeneous_scale {U : Set E} (hU : IsOpen U)
    {g : E × W → ℝ} (hg : ∀ x ∈ U, ∀ w, DifferentiableAt ℝ g (x,w))
    (hh : ∀ x ∈ U, ∀ r : ℝ, 0 < r → ∀ w, g (x,r • w) = r^2 * g (x,w))
    {x : E} (hx : x ∈ U) {r : ℝ} (hr : 0 < r) (w : W) :
    baseDifferential g x (r • w) = r^2 • baseDifferential g x w := by
  have hd₁ := (hg x hx (r • w)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜:=ℝ) x (r • w))
  have hd₂ := ((hg x hx w).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜:=ℝ) x w)).const_smul (r^2)
  have heq : (fun y : E => g (y,r • w)) =ᶠ[𝓝 x] (fun y : E => r^2 • g (y,w)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hh y hy r hr w
  exact (hd₁.congr_of_eventuallyEq heq.symm).unique hd₂

lemma verticalDifferential_homogeneous_scale {g : E × W → ℝ} {x : E}
    (hg : ∀ w, DifferentiableAt ℝ g (x,w))
    (hh : ∀ r : ℝ, 0 < r → ∀ w, g (x,r • w) = r^2 * g (x,w))
    {r : ℝ} (hr : 0 < r) (w : W) :
    verticalDifferential g x (r • w) = r • verticalDifferential g x w := by
  have hd₁ := ((hg (r • w)).hasFDerivAt.comp (r • w)
    (hasFDerivAt_prodMk_right (𝕜:=ℝ) x (r • w))).comp w
      ((ContinuousLinearMap.id ℝ W).hasFDerivAt.const_smul r)
  have hd₂ := ((hg w).hasFDerivAt.comp w
    (hasFDerivAt_prodMk_right (𝕜:=ℝ) x w)).const_smul (r^2)
  have heq : (fun v : W => g (x,r • v)) = (fun v : W => r^2 • g (x,v)) :=
    funext (hh r hr)
  change HasFDerivAt (fun v : W => g (x,r • v)) _ w at hd₁
  rw [heq] at hd₁
  have hd := hd₁.unique hd₂
  ext v
  have hv := congrArg (fun L : W →L[ℝ] ℝ => L v) hd
  simp only [comp_apply,smul_apply,id_apply,map_smul,smul_eq_mul] at hv ⊢
  change (fderiv ℝ g (x,r • w)) (0,v) = r * (fderiv ℝ g (x,w)) (0,v)
  simpa only [inr_apply] using (show (fderiv ℝ g (x,r • w)) ((inr ℝ E W) v) =
    r * (fderiv ℝ g (x,w)) ((inr ℝ E W) v) by nlinarith [hr.ne'])

lemma compact_positive_lower {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K)
    (hp : ∀ x ∈ K, 0 < f x) : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ f x := by
  let S : Set ℝ := insert 1 (f '' K)
  have hS : IsCompact S := (hK.image_of_continuousOn hf).insert 1
  obtain ⟨c,hc,hmin⟩ := hS.exists_isMinOn (by exact ⟨1,mem_insert _ _⟩)
    continuous_id.continuousOn
  have hcp : 0 < c := by
    rcases hc with h | ⟨x,hx,rfl⟩
    · simpa only [h] using (show (0:ℝ) < 1 by norm_num)
    · exact hp x hx
  exact ⟨c,hcp,fun x hx => hmin (mem_insert_of_mem 1 (mem_image_of_mem f hx))⟩

variable [ProperSpace W]

theorem tameOn_of_compact_homogeneous_tail {U U₀ K : Set E} (hU₀ : IsOpen U₀)
    (hK : IsCompact K) (hUK : U ⊆ K) (hKU : K ⊆ U₀)
    {F g : E × W → ℝ}
    (hF : ∀ x ∈ U₀, ∀ w, ContDiffAt ℝ ∞ F (x,w))
    (hg : ∀ x ∈ U₀, ∀ w, ContDiffAt ℝ 1 g (x,w))
    (hh : ∀ x ∈ U₀, ∀ r : ℝ, 0 < r → ∀ w, g (x,r • w) = r^2 * g (x,w))
    (hreg : ∀ x ∈ K, ∀ w, w ≠ 0 → verticalDifferential g x w ≠ 0)
    (R : ℝ) (htail : ∀ x ∈ U₀, ∀ w, R ≤ ‖w‖ → F (x,w) = g (x,w)) :
    TameOn U F g := by
  have hgd : ∀ x ∈ U₀, ∀ w, DifferentiableAt ℝ g (x,w) :=
    fun x hx w => (hg x hx w).differentiableAt one_ne_zero
  have hb : ∀ q : E × W, q.1 ∈ U₀ → ContinuousAt (fun y : E × W =>
      baseDifferential g y.1 y.2) q := by
    intro q hq
    exact (((compL ℝ E (E × W) ℝ).flip (inl ℝ E W)).continuous.continuousAt).comp
      ((hg q.1 hq q.2).continuousAt_fderiv one_ne_zero)
  have hv : ∀ q : E × W, q.1 ∈ U₀ → ContinuousAt (fun y : E × W =>
      verticalDifferential g y.1 y.2) q := by
    intro q hq
    exact (((compL ℝ W (E × W) ℝ).flip (inr ℝ E W)).continuous.continuousAt).comp
      ((hg q.1 hq q.2).continuousAt_fderiv one_ne_zero)
  let S : Set (E × W) := K ×ˢ Metric.sphere (0:W) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  obtain ⟨c,hc,hclow⟩ := compact_positive_lower hS
    (show ContinuousOn (fun q : E × W => ‖verticalDifferential g q.1 q.2‖) S from
      fun q hq => (hv q (hKU hq.1)).norm.continuousWithinAt)
    (by
      intro q hq
      apply norm_pos_iff.mpr (hreg q.1 hq.1 q.2 _)
      have hun : ‖q.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hq.2
      exact norm_ne_zero_iff.mp (by rw [hun]; norm_num))
  obtain ⟨C,hCb⟩ := hS.exists_bound_of_continuousOn
    (show ContinuousOn (fun q : E × W => baseDifferential g q.1 q.2) S from
      fun q hq => (hb q (hKU hq.1)).continuousWithinAt)
  have hlow : ∀ x ∈ U, ∀ w, c * ‖w‖ ≤ ‖verticalDifferential g x w‖ := by
    intro x hx w
    by_cases hw : w = 0
    · simp [hw]
    have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let u : W := ‖w‖⁻¹ • w
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,ne_of_gt hp]
    have hru : ‖w‖ • u = w := by simp [u,smul_smul,ne_of_gt hp]
    have hmin := hclow (x,u) ⟨hUK hx,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
    have he := verticalDifferential_homogeneous_scale (hgd x (hKU (hUK hx)))
      (hh x (hKU (hUK hx))) hp u
    rw [hru] at he
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hp]
    nlinarith
  have hbase : ∀ x ∈ U, ∀ w, ‖baseDifferential g x w‖ ≤ max C 0 * ‖w‖^2 := by
    intro x hx w
    by_cases hw : w = 0
    · subst w
      have he := congrArg norm (baseDifferential_homogeneous_scale hU₀ hgd hh
        (hKU (hUK hx)) (by norm_num : (0:ℝ) < 2) (0:W))
      simp only [smul_zero,norm_smul,Real.norm_eq_abs] at he
      norm_num at he
      simp only [norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero]
      nlinarith [norm_nonneg (baseDifferential g x 0)]
    have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let u : W := ‖w‖⁻¹ • w
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,ne_of_gt hp]
    have hru : ‖w‖ • u = w := by simp [u,smul_smul,ne_of_gt hp]
    have hmax := hCb (x,u) ⟨hUK hx,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
    have he := baseDifferential_homogeneous_scale hU₀ hgd hh (hKU (hUK hx)) hp u
    rw [hru] at he
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg ‖w‖,le_max_left C 0]
  let R₀ : ℝ := max R 1
  let D : Set (E × W) := K ×ˢ Metric.closedBall (0:W) R₀
  have hD : IsCompact D := hK.prod (isCompact_closedBall 0 R₀)
  have herr : ∀ q : E × W, q.1 ∈ U₀ → ContDiffAt ℝ 1 (F-g) q := by
    intro q hq
    exact ((hF q.1 hq q.2).of_le (by simp)).sub (hg q.1 hq q.2)
  obtain ⟨M₀,hM₀⟩ := hD.exists_bound_of_continuousOn
    (show ContinuousOn (F-g) D from fun q hq => (herr q (hKU hq.1)).continuousAt.continuousWithinAt)
  obtain ⟨M₁,hM₁⟩ := hD.exists_bound_of_continuousOn (f:=fderiv ℝ (F-g))
    (show ContinuousOn (fderiv ℝ (F-g)) D from
      fun q hq => ((herr q (hKU hq.1)).continuousAt_fderiv one_ne_zero).continuousWithinAt)
  have hzero : ∀ q : E × W, q.1 ∈ U → R₀ < ‖q.2‖ → (F-g) =ᶠ[𝓝 q] (fun _ => 0) := by
    intro q hq hR
    have hr : R < ‖q.2‖ := (le_max_left R 1).trans_lt hR
    filter_upwards [continuousAt_fst (hU₀.mem_nhds (hKU (hUK hq))),
      (continuousAt_const.eventually_lt continuous_snd.norm.continuousAt hr)] with y hy₁ hy₂
    exact sub_eq_zero.mpr (htail y.1 hy₁ y.2 hy₂.le)
  refine ⟨fun x hx w => hF x (hKU (hUK hx)) w,
    fun x hx w => hg x (hKU (hUK hx)) w,
    fun x hx => hh x (hKU (hUK hx)),c,max C 0,max M₀ 0,max M₁ 0,
    hc,le_max_right _ _,le_max_right _ _,le_max_right _ _,hlow,hbase,?_,?_⟩
  · intro q hq
    by_cases hr : ‖q.2‖ ≤ R₀
    · exact (hM₀ q ⟨hUK hq,by simpa only [Metric.mem_closedBall,dist_zero_right] using hr⟩).trans
        (le_max_left _ _)
    · have hz := (hzero q hq (lt_of_not_ge hr)).self_of_nhds
      change ‖(F-g) q‖ ≤ _
      rw [hz,norm_zero]
      exact le_max_right _ _
  · intro q hq
    by_cases hr : ‖q.2‖ ≤ R₀
    · exact (hM₁ q ⟨hUK hq,by simpa only [Metric.mem_closedBall,dist_zero_right] using hr⟩).trans
        (le_max_left _ _)
    · rw [Filter.EventuallyEq.fderiv_eq (hzero q hq (lt_of_not_ge hr)),fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.opNorm_zero]
      exact le_max_right _ _

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter SmoothFlow
open scoped ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma flatTimeField_spatial_support {X : ℝ × E → E} {S : Set E}
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => X (t,x)) ⊆ S) (t : ℝ) :
    Function.support (fun x => flatTimeField X (t,x)) ⊆ S := by
  intro x hx
  apply hs (Real.smoothTransition t) (smoothTime_mem t)
  change X (Real.smoothTransition t,x) ≠ 0
  intro hz
  exact hx (by simp only [flatTimeField,hz,smul_zero])

theorem exists_flat_smooth_evolution {X : ℝ × E → E}
    (hX : ContDiffOn ℝ ∞ X (Icc (0:ℝ) 1 ×ˢ univ))
    {S : Set E} (hS : IsCompact S)
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => X (t,x)) ⊆ S) :
    ∃ (K : ℝ≥0) (φ : ODE.CompleteFlow (timeLift (flatTimeField X))),
      LipschitzWith K (flatTimeField X) ∧ ContDiff ℝ ∞ (evolution φ) ∧
      ∀ s t, Function.support (fun x => evolution φ ((s,x),t)-x) ⊆ S := by
  have hflat := contDiff_flatTimeField hX
  obtain ⟨L,K,hL,hK⟩ := compact_map_bounds (compactSupport_flatTimeField hS hs)
    (hflat.of_le (by simp))
  obtain ⟨φ,hφ⟩ := exists_smooth_evolution hflat hL hK
  exact ⟨K,φ,hK,hφ,fun s t => evolution_support φ hK (flatTimeField_spatial_support hs) s t⟩

omit [CompleteSpace E] in

lemma flat_evolution_agrees {X : ℝ × E → E}
    (φ : ODE.CompleteFlow (timeLift (flatTimeField X))) {K : ℝ≥0}
    (hK : LipschitzWith K (flatTimeField X)) {y : ℝ → E}
    (hy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt y (X (t,y t)) (Icc (0:ℝ) 1) t)
    (t : ℝ) : evolution φ ((0,y 0),t) = y (Real.smoothTransition t) := by
  apply evolution_unique φ hK (y := fun t => y (Real.smoothTransition t))
    (s := 0) (fun t => flatTime_solution hy t) ?_ t
  simp only [Real.smoothTransition.zero_of_nonpos le_rfl]

omit [CompleteSpace E] in
lemma flat_evolution_endpoint {X : ℝ × E → E}
    (φ : ODE.CompleteFlow (timeLift (flatTimeField X))) {K : ℝ≥0}
    (hK : LipschitzWith K (flatTimeField X)) {y : ℝ → E}
    (hy : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt y (X (t,y t)) (Icc (0:ℝ) 1) t) :
    evolution φ ((0,y 0),1) = y 1 := by
  simpa only [Real.smoothTransition.one_of_one_le le_rfl] using flat_evolution_agrees φ hK hy 1

end NearbyLagrangian.Transport

end

end OAI
