import Mathlib
import OAI.Geometry.NearbyLagrangian.FamilyApproximation
import OAI.Geometry.NearbyLagrangian.RadialBlending

namespace OAI

/-! Smooth restoration of prescribed homogeneous tails and critical jets. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.InfinityRestore

open Filter Set ContinuousLinearMap
open scoped Topology ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [HasContDiffBump V]

def restoreFamily (A : ℝ) (F G : E × V → ℝ) (q : E × V) : ℝ :=
  blend (radialCutoff A) (fun w => F (q.1,w)) (fun w => G (q.1,w)) q.2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma restoreFamily_eq_inner {A : ℝ} (hA : 0 < A) (F G : E × V → ℝ)
    {q : E × V} (hq : ‖q.2‖ ≤ A) : restoreFamily A F G q = F q :=
  blend_radial_eq_inner hA _ _ hq

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma restoreFamily_eq_outer {A : ℝ} (hA : 0 < A) (F G : E × V → ℝ)
    {q : E × V} (hq : 2*A ≤ ‖q.2‖) : restoreFamily A F G q = G q :=
  blend_radial_eq_outer hA _ _ hq

omit [NormedSpace ℝ E] in

lemma restoreFamily_near_inner {A : ℝ} (hA : 0 < A) (F G : E × V → ℝ)
    {q : E × V} (hq : ‖q.2‖ < A) : restoreFamily A F G =ᶠ[𝓝 q] F := by
  filter_upwards [continuous_snd.norm.continuousAt.eventually_lt continuousAt_const hq]
    with r hr
  exact restoreFamily_eq_inner hA F G hr.le

omit [NormedSpace ℝ E] in
lemma restoreFamily_near_outer {A : ℝ} (hA : 0 < A) (F G : E × V → ℝ)
    {q : E × V} (hq : 2*A < ‖q.2‖) : restoreFamily A F G =ᶠ[𝓝 q] G := by
  filter_upwards [continuousAt_const.eventually_lt continuous_snd.norm.continuousAt hq]
    with r hr
  exact restoreFamily_eq_outer hA F G hr.le

lemma contDiffAt_restoreFamily {A : ℝ} (hA : 0 < A) {F G : E × V → ℝ}
    {q : E × V} (hF : ContDiffAt ℝ ∞ F q)
    (hG : q.2 ≠ 0 → ContDiffAt ℝ ∞ G q) :
    ContDiffAt ℝ ∞ (restoreFamily A F G) q := by
  by_cases hw : q.2 = 0
  · exact hF.congr_of_eventuallyEq
      (restoreFamily_near_inner hA F G (by simpa only [hw,norm_zero] using hA))
  · have hcut : ContDiffAt ℝ ∞ (fun r : E × V => radialCutoff A r.2) q :=
      (contDiff_radialCutoff A).contDiffAt.comp q contDiffAt_snd
    exact ((contDiffAt_const.sub hcut).mul hF).add (hcut.mul (hG hw))

lemma restoreFamily_jets {A : ℝ} (hA : 0 < A) (F G : E × V → ℝ)
    {q : E × V} (hq : ‖q.2‖ < A) :
    fderiv ℝ (restoreFamily A F G) q = fderiv ℝ F q ∧
      fderiv ℝ (fun r => (fderiv ℝ (restoreFamily A F G) r).comp (inr ℝ E V)) q =
        fderiv ℝ (fun r => (fderiv ℝ F r).comp (inr ℝ E V)) q := by
  have he := restoreFamily_near_inner hA F G hq
  refine ⟨he.fderiv_eq, ?_⟩
  have hv : (fun r => (fderiv ℝ (restoreFamily A F G) r).comp (inr ℝ E V)) =ᶠ[𝓝 q]
      (fun r => (fderiv ℝ F r).comp (inr ℝ E V)) :=
    he.fderiv.mono (fun _ h => congrArg (fun L => L.comp (inr ℝ E V)) h)
  exact hv.fderiv_eq

omit [NormedSpace ℝ E] in

theorem restoreFamily_critical_and_jets {U : Set E} {F G₀ G : E × V → ℝ}
    {A c M₀ M₁ B e d : ℝ} (hA : 1 ≤ A) (hc : 0 < c)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hunit : ∀ w : V, ‖fderiv ℝ (unitBump (E := V)) w‖ ≤ B)
    (hscale : (M₁+B*M₀)/A + e + 2*B*d < c) (hinner : M₁/c < A)
    (hF : ∀ X ∈ U, Differentiable ℝ (fun w => F (X,w)))
    (hG : ∀ X ∈ U, ∀ w ≠ 0, DifferentiableAt ℝ (fun w => G (X,w)) w)
    (h₀ : ∀ X ∈ U, ∀ w, c*‖w‖ ≤ ‖fderiv ℝ (fun w => G₀ (X,w)) w‖)
    (h₁ : ∀ X ∈ U, ∀ w, ‖fderiv ℝ (fun w => F (X,w)) w -
      fderiv ℝ (fun w => G₀ (X,w)) w‖ ≤ M₁)
    (hg : ∀ X ∈ U, ∀ w, ‖fderiv ℝ (fun w => G (X,w)) w -
      fderiv ℝ (fun w => G₀ (X,w)) w‖ ≤ e*‖w‖)
    (hv : ∀ X ∈ U, ∀ w, |G (X,w)-F (X,w)| ≤ M₀+d*‖w‖^2)
    (X : E) (hX : X ∈ U) (w : V) :
    (fderiv ℝ (fun w => restoreFamily A F G (X,w)) w = 0 ↔
      fderiv ℝ (fun w => F (X,w)) w = 0) ∧
    (fderiv ℝ (fun w => F (X,w)) w = 0 →
      restoreFamily A F G =ᶠ[𝓝 (X,w)] F) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have H := blend_radial_preserves_critical hA hc hM₀ hM₁ hB hd hunit
    hscale hinner (hF X hX) (hG X hX) (h₀ X hX) (h₁ X hX) (hg X hX) (hv X hX) w
  refine ⟨H.1, fun hw => ?_⟩
  exact restoreFamily_near_inner hAp F G
    ((critical_radius_bound hc (h₀ X hX) (h₁ X hX) hw).trans_lt hinner)

end NearbyLagrangian.InfinityRestore

namespace NearbyLagrangian.InfinityRestore

open Filter Set ContinuousLinearMap
open scoped Topology ContDiff

lemma exists_restoration_radius_above {c M₀ M₁ B e d R : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hB : 0 ≤ B)
    (hgap : e + 2*B*d < c) :
    ∃ A : ℝ, 1 ≤ A ∧ R < A ∧ M₁/c < A ∧
      (M₁+B*M₀)/A + e + 2*B*d < c := by
  obtain ⟨A,hA,hi,hs⟩ := exists_restoration_radius (M₀ := M₀) (M₁ := M₁) hgap
  refine ⟨max A (R+1), hA.trans (le_max_left _ _), ?_,
    hi.trans_le (le_max_left _ _), ?_⟩
  · exact (lt_add_one R).trans_le (le_max_right _ _)
  · have hq : (M₁+B*M₀)/max A (R+1) ≤ (M₁+B*M₀)/A :=
      div_le_div_of_nonneg_left (by positivity) (lt_of_lt_of_le zero_lt_one hA) (le_max_left _ _)
    exact (add_le_add (add_le_add hq le_rfl) le_rfl).trans_lt hs

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [HasContDiffBump V]

theorem exists_restored_family {U : Set E} {F G₀ G : E × V → ℝ}
    {c M₀ M₁ B e d R : ℝ} (hc : 0 < c)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hunit : ∀ w : V, ‖fderiv ℝ (unitBump (E := V)) w‖ ≤ B)
    (hgap : e + 2*B*d < c)
    (hF : ∀ q : E × V, q.1 ∈ U → ContDiffAt ℝ ∞ F q)
    (hG : ∀ q : E × V, q.1 ∈ U → q.2 ≠ 0 → ContDiffAt ℝ ∞ G q)
    (h₀ : ∀ X ∈ U, ∀ w, c*‖w‖ ≤ ‖fderiv ℝ (fun w => G₀ (X,w)) w‖)
    (h₁ : ∀ X ∈ U, ∀ w, ‖fderiv ℝ (fun w => F (X,w)) w -
      fderiv ℝ (fun w => G₀ (X,w)) w‖ ≤ M₁)
    (hg : ∀ X ∈ U, ∀ w, ‖fderiv ℝ (fun w => G (X,w)) w -
      fderiv ℝ (fun w => G₀ (X,w)) w‖ ≤ e*‖w‖)
    (hv : ∀ X ∈ U, ∀ w, |G (X,w)-F (X,w)| ≤ M₀+d*‖w‖^2) :
    ∃ (A : ℝ) (H : E × V → ℝ), 1 ≤ A ∧ R < A ∧
      (∀ q, q.1 ∈ U → ContDiffAt ℝ ∞ H q) ∧
      (∀ q, ‖q.2‖ ≤ R → H q = F q) ∧
      (∀ q, 2*A ≤ ‖q.2‖ → H q = G q) ∧
      (∀ X ∈ U, ∀ w, (fderiv ℝ (fun w => H (X,w)) w = 0 ↔
        fderiv ℝ (fun w => F (X,w)) w = 0)) ∧
      (∀ X ∈ U, ∀ w, fderiv ℝ (fun w => F (X,w)) w = 0 → H =ᶠ[𝓝 (X,w)] F) := by
  obtain ⟨A,hA,hRA,hi,hs⟩ := exists_restoration_radius_above
    (R := R) hM₀ hM₁ hB hgap
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hFd : ∀ X ∈ U, Differentiable ℝ (fun w => F (X,w)) := by
    intro X hX w
    exact ((hF (X,w) hX).differentiableAt (by simp)).comp w
      (differentiableAt_const X |>.prodMk differentiableAt_id)
  have hGd : ∀ X ∈ U, ∀ w ≠ 0, DifferentiableAt ℝ (fun w => G (X,w)) w := by
    intro X hX w hw
    exact ((hG (X,w) hX hw).differentiableAt (by simp)).comp w
      (differentiableAt_const X |>.prodMk differentiableAt_id)
  have Hcritical := restoreFamily_critical_and_jets hA hc hM₀ hM₁ hB hd hunit hs hi
    hFd hGd h₀ h₁ hg hv
  refine ⟨A,restoreFamily A F G,hA,hRA,?_,?_,?_,?_,?_⟩
  · exact fun q hq => contDiffAt_restoreFamily hAp (hF q hq) (hG q hq)
  · exact fun q hq => restoreFamily_eq_inner hAp F G (hq.trans hRA.le)
  · exact fun q hq => restoreFamily_eq_outer hAp F G hq
  · exact fun X hX w => (Hcritical X hX w).1
  · exact fun X hX w => (Hcritical X hX w).2

omit [HasContDiffBump V] in

lemma fiber_jets_of_eventuallyEq {F H : E × V → ℝ} {q : E × V}
    (h : H =ᶠ[𝓝 q] F) :
    (fderiv ℝ H q).comp (inr ℝ E V) = (fderiv ℝ F q).comp (inr ℝ E V) ∧
    fderiv ℝ (fun q => (fderiv ℝ H q).comp (inr ℝ E V)) q =
      fderiv ℝ (fun q => (fderiv ℝ F q).comp (inr ℝ E V)) q := by
  have hv : (fun r => (fderiv ℝ H r).comp (inr ℝ E V)) =ᶠ[𝓝 q]
      (fun r => (fderiv ℝ F r).comp (inr ℝ E V)) :=
    h.fderiv.mono (fun _ he => congrArg (fun L => L.comp (inr ℝ E V)) he)
  exact ⟨hv.eq_of_nhds,hv.fderiv_eq⟩

end NearbyLagrangian.InfinityRestore

namespace NearbyLagrangian.InfinityRestore
open Filter Set ContinuousLinearMap
open scoped Topology ContDiff Manifold
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [HasContDiffBump V]
variable {B : Type*} [TopologicalSpace B]

lemma restoreFamily_joint_germ {A : ℝ} (hA : 0 < A) (F G : B × V → ℝ)
    {q : B × V} (hq : ‖q.2‖ < A) : restoreFamily A F G =ᶠ[𝓝 q] F := by
  filter_upwards [continuous_snd.norm.continuousAt.eventually_lt continuousAt_const hq] with r hr
  exact restoreFamily_eq_inner hA F G hr.le

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Z] {I : ModelWithCorners ℝ E Z} [ChartedSpace Z B]

lemma contMDiffAt_restoreFamily {A : ℝ} (hA : 0 < A) {F G : B × V → ℝ}
    {q : B × V} (hF : ContMDiffAt (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ F q)
    (hG : q.2 ≠ 0 → ContMDiffAt (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ G q) :
    ContMDiffAt (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ (restoreFamily A F G) q := by
  by_cases hw : q.2 = 0
  · exact hF.congr_of_eventuallyEq
      (restoreFamily_joint_germ hA F G (by simpa only [hw,norm_zero] using hA))
  · have hcut : ContMDiffAt (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞
        (fun r : B × V => radialCutoff A r.2) q :=
      (contDiff_radialCutoff A).contMDiff.contMDiffAt.comp q contMDiffAt_snd
    exact ((contMDiffAt_const.sub hcut).mul hF).add (hcut.mul (hG hw))

theorem exists_restored_manifold_family {F G₀ G : B × V → ℝ}
    {c M₀ M₁ D e d R : ℝ} (hc : 0 < c)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hunit : ∀ w : V, ‖fderiv ℝ (unitBump (E := V)) w‖ ≤ D)
    (hgap : e + 2*D*d < c)
    (hF : ContMDiff (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ F)
    (hG : ∀ q : B × V, q.2 ≠ 0 → ContMDiffAt (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ G q)
    (h₀ : ∀ X w, c*‖w‖ ≤ ‖fderiv ℝ (fun w => G₀ (X,w)) w‖)
    (h₁ : ∀ X w, ‖fderiv ℝ (fun w => F (X,w)) w -
      fderiv ℝ (fun w => G₀ (X,w)) w‖ ≤ M₁)
    (hg : ∀ X w, ‖fderiv ℝ (fun w => G (X,w)) w -
      fderiv ℝ (fun w => G₀ (X,w)) w‖ ≤ e*‖w‖)
    (hv : ∀ X w, |G (X,w)-F (X,w)| ≤ M₀+d*‖w‖^2) :
    ∃ (A : ℝ) (H : B × V → ℝ), 1 ≤ A ∧ R < A ∧
      ContMDiff (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, ‖q.2‖ ≤ R → H q = F q) ∧
      (∀ q, 2*A ≤ ‖q.2‖ → H q = G q) ∧
      (∀ X w, (fderiv ℝ (fun w => H (X,w)) w = 0 ↔
        fderiv ℝ (fun w => F (X,w)) w = 0)) ∧
      (∀ X w, fderiv ℝ (fun w => F (X,w)) w = 0 → H =ᶠ[𝓝 (X,w)] F) := by
  obtain ⟨A,hA,hRA,hi,hs⟩ := exists_restoration_radius_above
    (R := R) hM₀ hM₁ hD hgap
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hFd (X : B) : Differentiable ℝ (fun w => F (X,w)) := by
    intro w
    exact ((hF.contMDiffAt.comp w
      (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt).differentiableAt (by simp)
  have hGd (X : B) (w : V) (hw : w ≠ 0) : DifferentiableAt ℝ (fun w => G (X,w)) w := by
    exact (((hG (X,w) hw).comp w
      (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt).differentiableAt (by simp)
  refine ⟨A,restoreFamily A F G,hA,hRA,?_,?_,?_,?_,?_⟩
  · exact fun q => contMDiffAt_restoreFamily hAp hF.contMDiffAt (hG q)
  · exact fun q hq => restoreFamily_eq_inner hAp F G (hq.trans hRA.le)
  · exact fun q hq => restoreFamily_eq_outer hAp F G hq
  · intro X w
    exact (blend_radial_preserves_critical hA hc hM₀ hM₁ hD hd hunit hs hi
      (hFd X) (hGd X) (h₀ X) (h₁ X) (hg X) (hv X) w).1
  · intro X w hw
    exact restoreFamily_joint_germ hAp F G
      ((critical_radius_bound hc (h₀ X) (h₁ X) hw).trans_lt hi)

end NearbyLagrangian.InfinityRestore

namespace NearbyLagrangian.InfinityRestore
open Filter Set ContinuousLinearMap
open scoped Topology ContDiff Manifold InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]
variable {E Z B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Z] {I : ModelWithCorners ℝ E Z}
  [TopologicalSpace B] [ChartedSpace Z B] [IsManifold I ∞ B] [T2Space B]
  [CompactSpace B] [Nonempty B]

theorem exists_smooth_homogeneous_tail {F : B × V → ℝ}
    (g₀ : C(B,Tubes.RegularHomogeneous V))
    (hF : ContMDiff (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ F)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hval : ∀ b w, ‖F (b,w)-g₀ b w‖ ≤ M₀)
    (hder : ∀ b w, ‖fderiv ℝ (fun w => F (b,w)) w-fderiv ℝ (g₀ b) w‖ ≤ M₁)
    (R : ℝ) :
    ∃ (A : ℝ) (g : C(B,Tubes.RegularHomogeneous V)) (H : B × V → ℝ),
      1 ≤ A ∧ R < A ∧ g₀.Homotopic g ∧
      (∀ q : B × V, q.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ (fun q => g q.1 q.2) q) ∧
      ContMDiff (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, ‖q.2‖ ≤ R → H q = F q) ∧
      (∀ q, 2*A ≤ ‖q.2‖ → H q = g q.1 q.2) ∧
      (∀ b w, (fderiv ℝ (fun w => H (b,w)) w = 0 ↔
        fderiv ℝ (fun w => F (b,w)) w = 0)) ∧
      (∀ b w, fderiv ℝ (fun w => F (b,w)) w = 0 → H =ᶠ[𝓝 (b,w)] F) := by
  obtain ⟨c,C,hc,_,hb⟩ := Tubes.RegularHomogeneous.uniform_gradient_bounds g₀.continuous
  have h₀ (b : B) (w : V) : c*‖w‖ ≤ ‖fderiv ℝ (g₀ b) w‖ := by
    have he : ‖fderiv ℝ (g₀ b) w‖ = ‖gradient (g₀ b) w‖ := by
      rw [← toDual_gradient]
      exact (InnerProductSpace.toDual ℝ V).norm_map _
    rw [he]
    exact (hb b w).1
  obtain ⟨D,hD,hunit⟩ := exists_unitBump_derivative_bound (E := V)
  let ε := c/(2*(1+2*D))
  have hden : 0 < 2*(1+2*D) := by positivity
  have hε : 0 < ε := div_pos hc hden
  have heq : ε*(2*(1+2*D)) = c := div_mul_cancel₀ c hden.ne'
  have hεc : ε < c := by nlinarith [mul_nonneg hD hε.le]
  have hgap : ε + 2*D*ε < c := by nlinarith
  have hm (b : B) (w : V) (hw : ‖w‖ = 1) : c ≤ ‖fderiv ℝ (g₀ b) w‖ := by
    simpa only [hw,mul_one] using h₀ b w
  obtain ⟨g,hhom,hgs,hclose⟩ :=
    Tubes.RegularHomogeneous.exists_smooth_homotopic_close (I := I) g₀ hc hε hεc hm
  have hv (b : B) (w : V) : |g b w-F (b,w)| ≤ M₀+ε*‖w‖^2 := by
    calc
      _ = ‖g b w-F (b,w)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖g b w-g₀ b w‖+‖g₀ b w-F (b,w)‖ := by
        simpa only [dist_eq_norm] using dist_triangle (g b w) (g₀ b w) (F (b,w))
      _ = ‖g b w-g₀ b w‖+‖F (b,w)-g₀ b w‖ := by rw [norm_sub_rev (g₀ b w)]
      _ ≤ ε*‖w‖^2+M₀ := add_le_add (hclose b w).1 (hval b w)
      _ = _ := add_comm _ _
  obtain ⟨A,H,hA,hRA,hHs,hHi,hHo,hHc,hHj⟩ := exists_restored_manifold_family
    (G₀ := fun q => g₀ q.1 q.2) (G := fun q => g q.1 q.2) (R := R)
    hc hM₀ hM₁ hD hε.le hunit hgap hF hgs h₀ hder (fun b w => (hclose b w).2) hv
  exact ⟨A,g,H,hA,hRA,hhom,hgs,hHs,hHi,hHo,hHc,hHj⟩

omit [Nontrivial V] [Nonempty B] in

theorem exists_smooth_homogeneous_tail_of_lower_bound {F : B × V → ℝ}
    (g₀ : C(B,Tubes.RegularHomogeneous V))
    (hF : ContMDiff (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ F)
    {c : ℝ} (hc : 0 < c)
    (h₀ : ∀ b w, c*‖w‖ ≤ ‖fderiv ℝ (g₀ b) w‖)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hval : ∀ b w, ‖F (b,w)-g₀ b w‖ ≤ M₀)
    (hder : ∀ b w, ‖fderiv ℝ (fun w => F (b,w)) w-fderiv ℝ (g₀ b) w‖ ≤ M₁)
    (R : ℝ) :
    ∃ (A : ℝ) (g : C(B,Tubes.RegularHomogeneous V)) (H : B × V → ℝ),
      1 ≤ A ∧ R < A ∧ g₀.Homotopic g ∧
      (∀ q : B × V, q.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ (fun q => g q.1 q.2) q) ∧
      ContMDiff (I.prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, ‖q.2‖ ≤ R → H q = F q) ∧
      (∀ q, 2*A ≤ ‖q.2‖ → H q = g q.1 q.2) ∧
      (∀ b w, (fderiv ℝ (fun w => H (b,w)) w = 0 ↔
        fderiv ℝ (fun w => F (b,w)) w = 0)) ∧
      (∀ b w, fderiv ℝ (fun w => F (b,w)) w = 0 → H =ᶠ[𝓝 (b,w)] F) := by
  obtain ⟨D,hD,hunit⟩ := exists_unitBump_derivative_bound (E := V)
  let ε := c/(2*(1+2*D))
  have hden : 0 < 2*(1+2*D) := by positivity
  have hε : 0 < ε := div_pos hc hden
  have heq : ε*(2*(1+2*D)) = c := div_mul_cancel₀ c hden.ne'
  have hεc : ε < c := by nlinarith [mul_nonneg hD hε.le]
  have hgap : ε + 2*D*ε < c := by nlinarith
  have hm (b : B) (w : V) (hw : ‖w‖ = 1) : c ≤ ‖fderiv ℝ (g₀ b) w‖ := by
    simpa only [hw,mul_one] using h₀ b w
  obtain ⟨g,hhom,hgs,hclose⟩ :=
    Tubes.RegularHomogeneous.exists_smooth_homotopic_close (I := I) g₀ hc hε hεc hm
  have hv (b : B) (w : V) : |g b w-F (b,w)| ≤ M₀+ε*‖w‖^2 := by
    calc
      _ = ‖g b w-F (b,w)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖g b w-g₀ b w‖+‖g₀ b w-F (b,w)‖ := by
        simpa only [dist_eq_norm] using dist_triangle (g b w) (g₀ b w) (F (b,w))
      _ = ‖g b w-g₀ b w‖+‖F (b,w)-g₀ b w‖ := by rw [norm_sub_rev (g₀ b w)]
      _ ≤ ε*‖w‖^2+M₀ := add_le_add (hclose b w).1 (hval b w)
      _ = _ := add_comm _ _
  obtain ⟨A,H,hA,hRA,hHs,hHi,hHo,hHc,hHj⟩ := exists_restored_manifold_family
    (G₀ := fun q => g₀ q.1 q.2) (G := fun q => g q.1 q.2) (R := R)
    hc hM₀ hM₁ hD hε.le hunit hgap hF hgs h₀ hder (fun b w => (hclose b w).2) hv
  exact ⟨A,g,H,hA,hRA,hhom,hgs,hHs,hHi,hHo,hHc,hHj⟩

end NearbyLagrangian.InfinityRestore

end

end OAI
