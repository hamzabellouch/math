import Mathlib
import OAI.Geometry.NearbyLagrangian.TameBounds
import OAI.Geometry.NearbyLagrangian.Restoration

namespace OAI

/-! Restriction and restoration of a tame family with one critical point. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport.TameOn
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology Manifold InnerProductSpace
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {U : Set E} {F g : E × W → ℝ} (T : TameOn U F g)

def referenceAt (x : E) (hx : x ∈ U) : Tubes.RegularHomogeneous W where
  toFun w := g (x,w)
  contDiff := contDiff_iff_contDiffAt.mpr fun w =>
    (T.smooth_g x hx w).comp w (contDiffAt_const.prodMk contDiffAt_id)
  homogeneity := T.homogeneous x hx
  regular := by
    intro w hw he
    obtain ⟨c,_,_,_,hc,_,_,_,hv,_⟩ := T.estimates
    have hd := verticalDifferential_eq_partial ((T.smooth_g x hx w).differentiableAt one_ne_zero)
    have hh := hv x hx w
    rw [hd,he,norm_zero] at hh
    exact (mul_pos hc (norm_pos_iff.mpr hw)).not_ge hh

@[simp] lemma referenceAt_apply (x : E) (hx : x ∈ U) (w : W) :
    T.referenceAt x hx w = g (x,w) := rfl

lemma referenceAt_fderiv (x : E) (hx : x ∈ U) (w : W) :
    fderiv ℝ (T.referenceAt x hx) w = verticalDifferential g x w :=
  (verticalDifferential_eq_partial ((T.smooth_g x hx w).differentiableAt one_ne_zero)).symm

lemma continuous_referenceAt {B : Type*} [TopologicalSpace B]
    {j : B → E} (hj : Continuous j) (hU : ∀ b, j b ∈ U) :
    Continuous (fun b => T.referenceAt (j b) (hU b)) := by
  have hcoord : Continuous (fun p : B × Metric.sphere (0:W) 1 => (j p.1,(p.2:W))) :=
    (hj.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  apply Tubes.RegularHomogeneous.continuous_of_joint_jet
  · change Continuous (fun p : B × Metric.sphere (0:W) 1 => g (j p.1,(p.2:W)))
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (T.smooth_g (j p.1) (hU p.1) p.2).continuousAt.comp (f := fun p : B × Metric.sphere (0:W) 1 => (j p.1,(p.2:W))) hcoord.continuousAt
  · simp only [referenceAt_fderiv,verticalDifferential]
    apply continuous_iff_continuousAt.mpr
    intro p
    have hd : ContinuousAt (fun p : B × Metric.sphere (0:W) 1 =>
        fderiv ℝ g (j p.1,(p.2:W))) p :=
      ((T.smooth_g (j p.1) (hU p.1) p.2).continuousAt_fderiv one_ne_zero).comp (f := fun p : B × Metric.sphere (0:W) 1 => (j p.1,(p.2:W))) hcoord.continuousAt
    exact hd.clm_comp continuousAt_const

def restrictedReference {B : Type*} [TopologicalSpace B]
    {j : B → E} (hj : Continuous j) (hU : ∀ b, j b ∈ U) :
    C(B,Tubes.RegularHomogeneous W) :=
  ⟨fun b => T.referenceAt (j b) (hU b), T.continuous_referenceAt hj hU⟩

lemma restricted_estimates {B : Type*} [TopologicalSpace B]
    {j : B → E} (hj : Continuous j) (hU : ∀ b, j b ∈ U) :
    ∃ c M₀ M₁ : ℝ, 0 < c ∧ 0 ≤ M₀ ∧ 0 ≤ M₁ ∧
      (∀ b w, c*‖w‖ ≤ ‖fderiv ℝ (T.restrictedReference hj hU b) w‖) ∧
      (∀ b w, ‖F (j b,w)-T.restrictedReference hj hU b w‖ ≤ M₀) ∧
      (∀ b w, ‖fderiv ℝ (fun w => F (j b,w)) w -
        fderiv ℝ (T.restrictedReference hj hU b) w‖ ≤ M₁) := by
  obtain ⟨c,_,M₀,M₁,hc,_,hM₀,hM₁,hv,_,hval,hder⟩ := T.estimates
  refine ⟨c,M₀,M₁,hc,hM₀,hM₁,?_,?_,?_⟩
  · intro b w
    exact (T.referenceAt_fderiv (j b) (hU b) w) ▸ hv (j b) (hU b) w
  · intro b w
    exact hval (j b,w) (hU b)
  · intro b w
    change ‖fderiv ℝ (fun w => F (j b,w)) w-fderiv ℝ (T.referenceAt (j b) (hU b)) w‖ ≤ _
    rw [T.referenceAt_fderiv,
      ← verticalDifferential_eq_partial ((T.smooth_F (j b) (hU b) w).differentiableAt (by simp)),
      ← verticalDifferential_sub (j b,w)
        ((T.smooth_F (j b) (hU b) w).differentiableAt (by simp))
        ((T.smooth_g (j b) (hU b) w).differentiableAt one_ne_zero)]
    exact (norm_verticalDifferential_le (F-g) (j b) w).trans (hder (j b,w) (hU b))

variable {V Z B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace Z] {I : ModelWithCorners ℝ V Z}
  [TopologicalSpace B] [ChartedSpace Z B]

include T in
lemma contMDiff_restrict {j : B → E} (hj : ContMDiff I 𝓘(ℝ,E) ∞ j)
    (hU : ∀ b, j b ∈ U) :
    ContMDiff (I.prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) ∞ (fun q : B × W => F (j q.1,q.2)) := by
  intro q
  exact (T.smooth_F (j q.1) (hU q.1) q.2).comp_contMDiffAt (f := fun q : B × W => (j q.1,q.2))
    ((hj.contMDiffAt.comp q contMDiffAt_fst).prodMk_space contMDiffAt_snd)

end NearbyLagrangian.Transport.TameOn

namespace NearbyLagrangian.Transport.TameOn
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology Manifold InnerProductSpace
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {U : Set E} {F g : E × W → ℝ} (T : TameOn U F g)
  {V Z B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace Z] {I : ModelWithCorners ℝ V Z}
  [TopologicalSpace B] [ChartedSpace Z B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]

theorem exists_restored_restriction {j : B → E}
    (hj : ContMDiff I 𝓘(ℝ,E) ∞ j) (hU : ∀ b, j b ∈ U) (R : ℝ) :
    ∃ (A : ℝ) (γ : C(B,Tubes.RegularHomogeneous W)) (H : B × W → ℝ),
      1 ≤ A ∧ R < A ∧ (T.restrictedReference hj.continuous hU).Homotopic γ ∧
      (∀ q : B × W, q.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) ∞ (fun q => γ q.1 q.2) q) ∧
      ContMDiff (I.prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, ‖q.2‖ ≤ R → H q = F (j q.1,q.2)) ∧
      (∀ q, 2*A ≤ ‖q.2‖ → H q = γ q.1 q.2) ∧
      (∀ b w, (fderiv ℝ (fun w => H (b,w)) w = 0 ↔
        verticalDifferential F (j b) w = 0)) ∧
      (∀ b w, verticalDifferential F (j b) w = 0 →
        H =ᶠ[𝓝 (b,w)] (fun q => F (j q.1,q.2))) := by
  obtain ⟨c,M₀,M₁,hc,hM₀,hM₁,hv,hval,hder⟩ := T.restricted_estimates hj.continuous hU
  obtain ⟨A,γ,H,hA,hRA,hhom,hgs,hHs,hHi,hHo,hHc,hHj⟩ :=
    InfinityRestore.exists_smooth_homogeneous_tail_of_lower_bound (I := I)
      (T.restrictedReference hj.continuous hU) (T.contMDiff_restrict hj hU)
      hc hv hM₀ hM₁ hval hder R
  refine ⟨A,γ,H,hA,hRA,hhom,hgs,hHs,hHi,hHo,?_,?_⟩
  · intro b w
    rw [verticalDifferential_eq_partial
      ((T.smooth_F (j b) (hU b) w).differentiableAt (by simp))]
    exact hHc b w
  · intro b w hw
    apply hHj b w
    rwa [verticalDifferential_eq_partial
      ((T.smooth_F (j b) (hU b) w).differentiableAt (by simp))] at hw

end NearbyLagrangian.Transport.TameOn

namespace NearbyLagrangian.Transport.TameOn
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology Manifold InnerProductSpace
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {U : Set E} {F g : E × W → ℝ} (T : TameOn U F g)

include T in

lemma partial_hessian_eq (x : E) (hx : x ∈ U) (w : W) :
    fderiv ℝ (fderiv ℝ (fun v => F (x,v))) w =
      (fderiv ℝ (fun q : E × W => verticalDifferential F q.1 q.2) (x,w)).comp
        (inr ℝ E W) := by
  have he : fderiv ℝ (fun v => F (x,v)) = fun v => verticalDifferential F x v := by
    funext v
    exact (verticalDifferential_eq_partial ((T.smooth_F x hx v).differentiableAt (by simp))).symm
  rw [he]
  have hd := (differentiableAt_verticalDifferential (T.smooth_F x hx w)).hasFDerivAt
  have hc : HasFDerivAt (fun v : W => (x,v)) (inr ℝ E W) w := by
    simpa only [ContinuousLinearMap.inr, id_eq] using (hasFDerivAt_const x w).prodMk (hasFDerivAt_id w)
  exact (hd.comp w hc).fderiv

variable [FiniteDimensional ℝ W]
  {V Z B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace Z] {I : ModelWithCorners ℝ V Z}
  [TopologicalSpace B] [ChartedSpace Z B] [IsManifold I ∞ B]
  [T2Space B] [CompactSpace B]

theorem exists_restored_single_critical {j : B → E}
    (hj : ContMDiff I 𝓘(ℝ,E) ∞ j) (hU : ∀ b, j b ∈ U)
    {s : E → W} (hs : ∀ x ∈ U, ContDiffAt ℝ ∞ s x)
    (hc : ∀ x ∈ U, ∀ w, verticalDifferential F x w = 0 ↔ w = s x)
    (hh : ∀ x ∈ U, Function.Bijective
      ((fderiv ℝ (fun q : E × W => verticalDifferential F q.1 q.2) (x,s x)).comp
        (inr ℝ E W))) (R : ℝ) :
    ∃ (A : ℝ) (γ : C(B,Tubes.RegularHomogeneous W)) (H : B × W → ℝ),
      1 ≤ A ∧ R < A ∧ (T.restrictedReference hj.continuous hU).Homotopic γ ∧
      (∀ q : B × W, q.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) ∞ (fun q => γ q.1 q.2) q) ∧
      ContMDiff (I.prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, ‖q.2‖ ≤ R → H q = F (j q.1,q.2)) ∧
      (∀ q, 2*A ≤ ‖q.2‖ → H q = γ q.1 q.2) ∧
      ContMDiff I 𝓘(ℝ,W) ∞ (s ∘ j) ∧
      (∀ b w, fderiv ℝ (fun w => H (b,w)) w = 0 ↔ w = s (j b)) ∧
      (∀ b, Function.Bijective (fderiv ℝ (fderiv ℝ (fun w => H (b,w))) (s (j b)))) := by
  obtain ⟨A,γ,H,hA,hRA,hhom,hgs,hHs,hHi,hHo,hHc,hHj⟩ :=
    T.exists_restored_restriction hj hU R
  refine ⟨A,γ,H,hA,hRA,hhom,hgs,hHs,hHi,hHo,?_,?_,?_⟩
  · intro b
    exact (hs (j b) (hU b)).comp_contMDiffAt hj.contMDiffAt
  · intro b w
    exact (hHc b w).trans (hc (j b) (hU b) w)
  · intro b
    have hcrit : verticalDifferential F (j b) (s (j b)) = 0 :=
      (hc (j b) (hU b) (s (j b))).mpr rfl
    have he : (fun w => H (b,w)) =ᶠ[𝓝 (s (j b))] (fun w => F (j b,w)) :=
      (hHj b (s (j b)) hcrit).comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    rw [he.fderiv.fderiv_eq,T.partial_hessian_eq (j b) (hU b)]
    exact hh (j b) (hU b)

end NearbyLagrangian.Transport.TameOn

end

end OAI
