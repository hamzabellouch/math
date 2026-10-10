import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI


namespace Release061
open Set Filter Metric
open scoped Topology

theorem hurwitz_zero_interior {S : Set ℂ} (hS : IsOpen S)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) S)
    (hne : ∀ᶠ j in atTop, ∀ z ∈ S, f j z ≠ 0)
    {p : ℂ} (hp : p ∈ S) (hgp : g p = 0) :
    ∀ᶠ z in 𝓝 p, g z = 0 := by
  have hg := hfg.differentiableOn hf hS
  rcases (hg.analyticAt (hS.mem_nhds hp)).eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · exact hz
  exfalso
  have he : ∀ᶠ z in 𝓝 p, z ≠ p → g z ≠ 0 := by
    simpa only [mem_compl_iff,mem_singleton_iff] using eventually_nhdsWithin_iff.mp hn
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (he.and (hS.mem_nhds hp))
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hcl : closedBall p r ⊆ S := by
    intro z hz
    exact (hsub (closedBall_subset_ball (by dsimp [r]; linarith) hz)).2
  have hnsp : ∀ z ∈ sphere p r, g z ≠ 0 := by
    intro z hz
    apply (hsub (closedBall_subset_ball (by dsimp [r]; linarith) (sphere_subset_closedBall hz))).1
    intro hzp
    have hd := mem_sphere.mp hz
    rw [hzp,dist_self] at hd
    linarith
  obtain ⟨z₀,hz₀,hmin⟩ := (isCompact_sphere p r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    ((hg.continuousOn.mono (sphere_subset_closedBall.trans hcl)).norm)
  let δ := ‖g z₀‖
  have hδ : 0 < δ := norm_pos_iff.mpr (hnsp z₀ hz₀)
  have hunif : TendstoUniformlyOn f g atTop (sphere p r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_sphere p r)).mp (hfg.mono (sphere_subset_closedBall.trans hcl))
  have hsmall : ∀ᶠ j in atTop, ‖f j p‖ < δ/2 := by
    have ht : Tendsto (fun j => ‖f j p‖) atTop (𝓝 0) := by
      simpa [hgp] using (hfg.tendsto_at hp).norm
    exact (tendsto_order.mp ht).2 (δ/2) (half_pos hδ)
  have hcontr : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards [hf,hne,hsmall,Metric.tendstoUniformlyOn_iff.mp hunif (δ/2) (half_pos hδ)] with j hj hjne hjs hju
    have hinv : DiffContOnCl ℂ (fun z => (f j z)⁻¹) (ball p r) :=
      DiffContOnCl.mk_ball ((hj.inv hjne).mono (ball_subset_closedBall.trans hcl))
        ((hj.continuousOn.inv₀ hjne).mono hcl)
    have hbound : ∀ z ∈ frontier (ball p r), ‖(f j z)⁻¹‖ ≤ (δ/2)⁻¹ := by
      intro z hz
      rw [frontier_ball p hr.ne'] at hz
      have htri := norm_le_norm_sub_add (g z) (f j z)
      have herr : ‖g z-f j z‖ < δ/2 := by simpa only [dist_eq_norm] using hju z hz
      have hm : δ ≤ ‖g z‖ := hmin hz
      have hlo : δ/2 ≤ ‖f j z‖ := by linarith
      rw [norm_inv]
      exact inv_anti₀ (half_pos hδ) hlo
    have hcenter := Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball : Bornology.IsBounded (ball p r)) hinv hbound
      (subset_closure (mem_ball_self hr))
    rw [norm_inv] at hcenter
    have hlo : δ/2 ≤ ‖f j p‖ := (inv_le_inv₀ (norm_pos_iff.mpr (hjne p hp)) (half_pos hδ)).mp hcenter
    linarith
  exact (Filter.Eventually.exists hcontr).choose_spec

theorem hurwitz_zero_interior_finiteDim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → ℂ} {g : E → ℂ}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) S)
    (hne : ∀ᶠ j in atTop, ∀ z ∈ S, f j z ≠ 0)
    {p : E} (hp : p ∈ S) (hgp : g p = 0) :
    ∀ᶠ z in 𝓝 p, g z = 0 := by
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hp)
  filter_upwards [ball_mem_nhds p (half_pos hR)] with y hy
  let l : ℂ → E := fun z => p+z • (y-p)
  have hl : Differentiable ℂ l := by
    intro z
    exact (differentiableAt_const p).add (differentiableAt_id.smul_const _)
  have hm : MapsTo l (ball 0 2) S := by
    intro z hz
    apply hsub
    rw [mem_ball,dist_eq_norm]
    have hy' : ‖y-p‖ < R/2 := by simpa only [mem_ball,dist_eq_norm] using hy
    have hz' : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
    simp only [l,add_sub_cancel_left,norm_smul]
    nlinarith [norm_nonneg z,norm_nonneg (y-p)]
  have hconv := hfg.comp l hm hl.continuous.continuousOn
  have hdiff : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j ∘ l) (ball 0 2) :=
    hf.mono fun j hj => hj.comp hl.differentiableOn hm
  have hnonzero : ∀ᶠ j in atTop, ∀ z ∈ ball 0 2, (f j ∘ l) z ≠ 0 :=
    hne.mono fun j hj z hz => hj (l z) (hm hz)
  have h0 : (g ∘ l) 0 = 0 := by simpa [l] using hgp
  have he := hurwitz_zero_interior isOpen_ball hconv hdiff hnonzero
    (mem_ball_self (by norm_num : (0:ℝ)<2)) h0
  have hg := (hconv.differentiableOn hdiff isOpen_ball).analyticOnNhd isOpen_ball
  have hall := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0:ℂ) 2).isPreconnected (mem_ball_self (by norm_num)) he
  have h1 := hall (by norm_num : (1:ℂ) ∈ ball 0 2)
  simpa [l,Function.comp_def] using h1

theorem hurwitz_zero_free_or_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set E} (hS : IsOpen S) (hconn : IsPreconnected S)
    {f : ℕ → E → ℂ} {g : E → ℂ}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) S)
    (hne : ∀ᶠ j in atTop, ∀ z ∈ S, f j z ≠ 0) :
    (∀ z ∈ S, g z ≠ 0) ∨ (∀ z ∈ S, g z = 0) := by
  by_cases hn : ∀ z ∈ S, g z ≠ 0
  · exact Or.inl hn
  right
  push Not at hn
  obtain ⟨p,hp,hgp⟩ := hn
  have hc := hfg.continuousOn (hf.mono fun _ hj => hj.continuousOn).frequently
  let Z := {z | z ∈ S ∧ g z = 0}
  let N := {z | z ∈ S ∧ g z ≠ 0}
  have hZ : IsOpen Z := isOpen_iff_mem_nhds.mpr fun z hz =>
    inter_mem (hS.mem_nhds hz.1)
      (hurwitz_zero_interior_finiteDim hS hfg hf hne hz.1 hz.2)
  have hN : IsOpen N := isOpen_iff_mem_nhds.mpr fun z hz =>
    inter_mem (hS.mem_nhds hz.1)
      (((hc z hz.1).continuousAt (hS.mem_nhds hz.1)).eventually_ne hz.2)
  have hdis : Disjoint Z N := Set.disjoint_left.mpr fun _ hz hn => hn.2 hz.2
  have hcover : S ⊆ Z ∪ N := by
    intro z hz
    by_cases hg : g z = 0
    · exact Or.inl ⟨hz,hg⟩
    · exact Or.inr ⟨hz,hg⟩
  have hsub := hconn.subset_left_of_subset_union hZ hN hdis hcover
    ⟨p,hp,hp,hgp⟩
  exact fun z hz => (hsub hz).2

end Release061



end OAI
