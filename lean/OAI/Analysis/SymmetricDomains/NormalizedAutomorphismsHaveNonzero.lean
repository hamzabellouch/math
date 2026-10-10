import Mathlib
import OAI.Analysis.SymmetricDomains.NormalizedAutomorphismLocalLimit
import OAI.Analysis.SymmetricDomains.NormalizedDisplacementZeroUniform

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem normalized_displacement_zero_of_local_zero
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0<h i) (hh : Tendsto h l (𝓝 0))
    (p : U) {R : ℝ} (hR : 0<R) (hRU : closedBall p.val R⊆U)
    (hstep : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ y∈closedBall p.val R,
      ‖(q i).ambientAut y-y‖≤ε*h i) :
    TendstoLocallyUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x))
      (fun _ => 0) l U := by
  let N : ι → ℕ := fun i => ⌊1/h i⌋₊
  let M : ι → ℕ := fun i => if h i≤1 then N i+1 else 0
  have hM (i : ι) : (M i:ℝ)*h i≤2 := by
    dsimp [M]
    split_ifs with hi
    · have hn : (N i:ℝ)*h i≤1 :=
        (le_div_iff₀ (hp i)).mp (Nat.floor_le (div_nonneg zero_le_one (hp i).le))
      push_cast
      nlinarith
    · simp
  have hhi : ∀ᶠ i in l, h i≤1 := (hh.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ hi => hi.le)
  apply normalized_displacement_zero_of_uniform_small_powers hU l q h hp N
  · exact Eventually.of_forall (fun i => by
      have hn := (div_lt_iff₀ (hp i)).mp (Nat.lt_floor_add_one (1/h i))
      dsimp [N]
      push_cast
      exact hn.le)
  · intro W hW
    have he := powers_eventually_mem_nhds_of_vanishing_normalized_displacement hU hc hbd Γ hhol l q h
      (fun i => (hp i).le) M (by norm_num : (0:ℝ)<2) hM p hR hRU hstep W hW
    filter_upwards [he,hhi] with i hi hhi
    simpa only [M,ite_eq_left hhi] using hi

theorem normalized_automorphisms_have_nonzero_complete_limit
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (q : ℕ → Biholomorph U U) (h : ℕ → ℝ) (hp : ∀ i, 0<h i)
    (hh : Tendsto h atTop (𝓝 0)) (p : U) {R : ℝ} (hR : 0<R)
    (hRU : closedBall p.val R⊆U)
    (hbound : ∀ i, ∀ x∈closedBall p.val R, ‖(q i).ambientAut x-x‖≤h i)
    (hmax : ∀ i, ∃ x∈closedBall p.val R, h i≤‖(q i).ambientAut x-x‖) :
    ∃ X : Affine n → Affine n, IsCompleteGenerator U X ∧ X≠0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun i x => (h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)) X atTop (ball p.val R) := by
  let f : ℕ → Affine n → Affine n := fun i x => (h i)⁻¹ • ((q i).ambientAut x-x)
  have hfd (i : ℕ) : DifferentiableOn ℂ (f i) U := by
    intro x hx
    exact ((((q i).ambientAut_analytic hU x hx).differentiableAt.sub
      differentiableAt_id).const_smul (h i)⁻¹).differentiableWithinAt
  have hfb (i : ℕ) (x : Affine n) (hx : x∈closedBall p.val R) : ‖f i x‖≤1 := by
    dsimp [f]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hp i)]
    calc
      _ ≤ (h i)⁻¹*h i := mul_le_mul_of_nonneg_left (hbound i x hx) (inv_nonneg.mpr (hp i).le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (hp i))
  obtain ⟨F,hFd,φ,hφ,hconv⟩ := montel_expanding_domains isOpen_ball f (by
    intro x hx
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
    exact ⟨r,hr,1,zero_lt_one,hrsub,Eventually.of_forall (fun i =>
      ⟨(hfd i).mono (hrsub.trans (ball_subset_closedBall.trans hRU)),
       fun y hy => hfb i y (ball_subset_closedBall (hrsub hy))⟩)⟩)
  have hFa : AnalyticOnNhd ℂ F (ball p.val R) := analyticOnNhd_of_differentiableOn_affine isOpen_ball hFd
  obtain ⟨H,hH0,hHc,hHm,hHF⟩ := normalized_automorphism_local_limit_complete hU hc hbd Γ hhol atTop
    (q ∘ φ) (h ∘ φ) (fun i => hp (φ i)) (hh.comp hφ.tendsto_atTop)
    (ball p.val R) isOpen_ball (convex_ball p.val R).isPreconnected (ball_subset_closedBall.trans hRU)
    p (mem_ball_self hR) F hFa hconv
  let X := infinitesimalGenerator H
  have hX : IsCompleteGenerator U X := ⟨H,hHc,hH0,hHm,rfl⟩
  refine ⟨X,hX,?_,φ,hφ,hconv.congr_right (fun x hx => (hHF hx).symm)⟩
  intro hzero
  have hFzero : EqOn F (fun _ => 0) (ball p.val R) := by
    intro x hx
    rw [← hHF hx]
    change X x=0
    rw [hzero]
    rfl
  have hz := hconv.congr_right hFzero
  have hsmall : closedBall p.val (R/2)⊆ball p.val R := closedBall_subset_ball (half_lt_self hR)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall p.val (R/2))).mp (hz.mono hsmall)
  have hstep : ∀ ε : ℝ, 0<ε → ∀ᶠ i in atTop, ∀ y∈closedBall p.val (R/2),
      ‖(q (φ i)).ambientAut y-y‖≤ε*h (φ i) := by
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with i hi
    intro y hy
    have he : (q (φ i)).ambientAut y-y=h (φ i) • f (φ i) y := by
      dsimp [f]
      rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (hp (φ i))),one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (hp (φ i))]
    have hv : ‖f (φ i) y‖≤ε := le_of_lt (by simpa only [dist_eq_norm,zero_sub,norm_neg] using hi y hy)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hv (hp (φ i)).le
  have hg := normalized_displacement_zero_of_local_zero hU hc hbd Γ hhol atTop (q ∘ φ) (h ∘ φ)
    (fun i => hp (φ i)) (hh.comp hφ.tendsto_atTop) p (half_pos hR)
    (hsmall.trans (ball_subset_closedBall.trans hRU)) hstep
  have hgu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall p.val R)).mp (hg.mono hRU)
  obtain ⟨i,hi⟩ := (Metric.tendstoUniformlyOn_iff.mp hgu 1 zero_lt_one).exists
  obtain ⟨x,hx,hmaxx⟩ := hmax (φ i)
  have hi' : ‖(h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)‖<1 := by
    simpa only [Function.comp_apply,dist_eq_norm,zero_sub,norm_neg] using hi x hx
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hp (φ i))] at hi'
  have hl : 1≤(h (φ i))⁻¹*‖(q (φ i)).ambientAut x-x‖ := by
    calc
      1 = (h (φ i))⁻¹*h (φ i) := (inv_mul_cancel₀ (ne_of_gt (hp (φ i)))).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmaxx (inv_nonneg.mpr (hp (φ i)).le)
  exact (not_lt_of_ge hl) hi'
end Biholomorph
end Release061

end

end OAI
