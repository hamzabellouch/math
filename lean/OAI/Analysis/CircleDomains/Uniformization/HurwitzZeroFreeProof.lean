import OAI.Analysis.CircleDomains.Uniformization.LimitConformality
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace OAI

/-! Discharge the zero-free Hurwitz input. A positive lower bound on a
circle bounds the reciprocals inside by maximum modulus. Isolated zeros
and the analytic identity principle then give the connected-domain form. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem nonzero_limit_center_of_nonzero_circle
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (sphere c r))
    (hF : ∀ᶠ n in atTop, DiffContOnCl ℂ (F n) (ball c r) ∧
      ∀ z ∈ closedBall c r, F n z ≠ 0)
    (hlim : TendstoUniformlyOn F f atTop (sphere c r))
    (hcenter : Tendsto (fun n => F n c) atTop (𝓝 (f c)))
    (hboundary : ∀ z ∈ sphere c r, f z ≠ 0) : f c ≠ 0 := by
  intro hz
  obtain ⟨a,ha,hbound⟩ := (isCompact_sphere c r).exists_forall_le' hcont.norm
    (fun z hz => norm_pos_iff.mpr (hboundary z hz))
  have hu := Metric.tendstoUniformlyOn_iff.mp hlim (a/2) (half_pos ha)
  have hs : ∀ᶠ n in atTop, ‖F n c‖ < a/2 := by
    have ht := hcenter.norm
    rw [hz,norm_zero] at ht
    exact ht.eventually (gt_mem_nhds (half_pos ha))
  obtain ⟨n,hn,hu,hs⟩ := (hF.and (hu.and hs)).exists
  have hnz := hn.2 c (mem_closedBall_self hr.le)
  have hd : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball c r) :=
    hn.1.inv (fun z hz => hn.2 z (closure_ball_subset_closedBall hz))
  have hmax : ‖(F n c)⁻¹‖ ≤ (a/2)⁻¹ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (by
      intro z hz
      rw [frontier_ball c hr.ne'] at hz
      have he := hu z hz
      have hb := hbound z hz
      have hlo : a/2 ≤ ‖F n z‖ := by
        have hd := norm_le_norm_add_norm_sub (F n z) (f z)
        rw [← dist_eq_norm,dist_comm (F n z)] at hd
        linarith
      rw [norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hn.2 z (sphere_subset_closedBall hz)))
        (half_pos ha)).mpr hlo)
      (subset_closure (mem_ball_self hr))
  rw [norm_inv] at hmax
  have hlo := (inv_le_inv₀ (norm_pos_iff.mpr hnz) (half_pos ha)).mp hmax
  exact (not_lt_of_ge hlo) hs

 theorem hurwitzZeroFreeLimit : HurwitzZeroFreeLimit := by
  intro D F f hD hconn hF hlim
  have hd : DifferentiableOn ℂ f D := hlim.differentiableOn (hF.mono (fun _ h => h.1)) hD
  have ha := hd.analyticOnNhd hD
  by_cases hzall : ∀ z ∈ D, f z = 0
  · exact Or.inl hzall
  right
  intro c hc hz
  have hn : ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 := by
    rcases (ha c hc).eventually_eq_zero_or_eventually_ne_zero with he | hn
    · exact (hzall (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn.isPreconnected hc he)).elim
    · exact hn
  obtain ⟨ε,hε,hεn⟩ := Metric.mem_nhdsWithin_iff.mp hn
  obtain ⟨δ,hδ,hδD⟩ := Metric.isOpen_iff.mp hD c hc
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := by dsimp [r]; have := min_le_left ε δ; linarith
  have hrδ : r < δ := by dsimp [r]; have := min_le_right ε δ; linarith
  have hbD : closedBall c r ⊆ D := fun z hz => hδD (closedBall_subset_ball hrδ hz)
  have hnz : ∀ z ∈ sphere c r, f z ≠ 0 := by
    intro z hz
    apply hεn
    refine ⟨closedBall_subset_ball hrε (sphere_subset_closedBall hz),?_⟩
    change z ≠ c
    intro he
    have hh := mem_sphere.mp hz
    rw [he,dist_self] at hh
    exact hr.ne' hh.symm
  have hfseq : ∀ᶠ n in atTop, DiffContOnCl ℂ (F n) (ball c r) ∧
      ∀ z ∈ closedBall c r, F n z ≠ 0 := hF.mono (fun n hn =>
    ⟨DiffContOnCl.mk_ball (hn.1.mono (ball_subset_closedBall.trans hbD))
      (hn.1.continuousOn.mono hbD),fun z hz => hn.2 z (hbD hz)⟩)
  have hU : TendstoUniformlyOn F f atTop (sphere c r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c r)).mp
      (hlim.mono (sphere_subset_closedBall.trans hbD))
  exact nonzero_limit_center_of_nonzero_circle hr
    (hd.continuousOn.mono (sphere_subset_closedBall.trans hbD)) hfseq hU (hlim.tendsto_at hc) hnz hz

end CircleDomainRigidity

end

end OAI
