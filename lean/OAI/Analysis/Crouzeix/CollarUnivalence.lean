import Mathlib
import OAI.Analysis.Crouzeix.BoundaryPatching

namespace OAI

/-! Collar Univalence. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem inverseBranch_into_domain {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : MapsTo g U (ball 0 1)) (hfront : ∀ p ∈ frontier U, ‖g p‖ = 1)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = g)
    {p : ℂ} (hp : p ∈ closure U) (hpe : p ∈ e.source)
    {δ : ℝ} (hδ : 0 < δ) (hδe : ball (g p) δ ⊆ e.target) :
    MapsTo e.symm (ball (g p) δ ∩ ball 0 1) U := by
  let L := ball (g p) δ ∩ ball 0 1
  have hLt : L ⊆ e.target := inter_subset_left.trans hδe
  have hconn : IsPreconnected (e.symm '' L) :=
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected.image _
      (e.continuousOn_symm.mono hLt)
  have hn : e.source ∩ g ⁻¹' ball (g p) δ ∈ 𝓝 p :=
    inter_mem (e.open_source.mem_nhds hpe)
      ((he ▸ e.continuousAt hpe).preimage_mem_nhds (ball_mem_nhds _ hδ))
  obtain ⟨x, hxN, hxU⟩ := (mem_closure_iff_nhds.mp hp) _ hn
  have hnon : (e.symm '' L ∩ U).Nonempty := by
    refine ⟨x, ⟨g x, ⟨hxN.2, hg hxU⟩, ?_⟩, hxU⟩
    simpa only [he] using e.left_inv hxN.1
  have hcl : closure U ∩ e.symm '' L ⊆ U := by
    rintro x ⟨hx, z, hz, rfl⟩
    by_contra hnU
    have hpF : e.symm z ∈ frontier U := ⟨hx, by simpa only [hU.interior_eq] using hnU⟩
    have hmod := hfront _ hpF
    have heq : g (e.symm z) = z := by simpa only [he] using e.right_inv (hLt hz)
    rw [heq] at hmod
    exact (ne_of_lt (mem_ball_zero_iff.mp hz.2)) hmod
  exact fun z hz => (hconn.subset_of_closure_inter_subset hU hnon hcl) ⟨z, hz, rfl⟩

theorem injOn_closure_of_boundary_modulus {U V : Set ℂ} (hU : IsOpen U)
    (hUV : closure U ⊆ V) {g : ℂ → ℂ} (hga : AnalyticOnNhd ℂ g V)
    (hbij : BijOn g U (ball 0 1))
    (hgd : ∀ p ∈ closure U, deriv g p ≠ 0)
    (hfront : ∀ p ∈ frontier U, ‖g p‖ = 1) : InjOn g (closure U) := by
  intro p hp q hq hpq
  let dp := ((hga p (hUV hp)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hgd p hp))
  let dq := ((hga q (hUV hq)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hgd q hq))
  let ep := dp.toOpenPartialHomeomorph g
  let eq := dq.toOpenPartialHomeomorph g
  have hps : p ∈ ep.source := dp.mem_toOpenPartialHomeomorph_source
  have hqs : q ∈ eq.source := dq.mem_toOpenPartialHomeomorph_source
  have hη : g p ∈ ep.target ∩ eq.target :=
    ⟨ep.map_source hps, hpq.symm ▸ eq.map_source hqs⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (ep.open_target.inter eq.open_target) (g p) hη
  let L := ball (g p) δ ∩ ball 0 1
  have hpU := inverseBranch_into_domain hU hbij.mapsTo hfront ep rfl hp hps hδ
    (hδsub.trans inter_subset_left)
  have hqU := inverseBranch_into_domain hU hbij.mapsTo hfront eq rfl hq hqs hδ
    (hpq ▸ hδsub.trans inter_subset_right)
  have heqL : EqOn ep.symm eq.symm L := by
    intro z hz
    have hzq : z ∈ ball (g q) δ ∩ ball 0 1 := hpq ▸ hz
    apply hbij.injOn (hpU hz) (hqU hzq)
    exact (ep.right_inv (hδsub hz.1).1).trans (eq.right_inv (hδsub hz.1).2).symm
  have hle : ‖g p‖ ≤ 1 := by
    by_cases hpU : p ∈ U
    · exact (mem_ball_zero_iff.mp (hbij.mapsTo hpU)).le
    · exact (hfront p ⟨hp, by simpa only [hU.interior_eq] using hpU⟩).le
  have hcl : g p ∈ closure L := by
    have hn : ball (g p) δ ∈ 𝓝 (g p) := ball_mem_nhds _ hδ
    have hc : g p ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0), mem_closedBall_zero_iff]
      exact hle
    exact mem_closure_iff_nhds.mpr fun N hN => by
      obtain ⟨z, hzN, hzD⟩ := mem_closure_iff_nhds.mp hc _ (inter_mem hN hn)
      exact ⟨z, hzN.1, hzN.2, hzD⟩
  have : NeBot (𝓝[L] (g p)) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have heq : ep.symm (g p) = eq.symm (g p) :=
    tendsto_nhds_unique ((ep.continuousAt_symm hη.1).continuousWithinAt.tendsto)
      (((eq.continuousAt_symm hη.2).continuousWithinAt.tendsto).congr'
        (heqL.eventuallyEq_of_mem self_mem_nhdsWithin).symm)
  have hlp : ep.symm (g p) = p := ep.left_inv hps
  have hlq : eq.symm (g q) = q := eq.left_inv hqs
  rw [hlp] at heq
  rw [hpq, hlq] at heq
  exact heq

theorem exists_univalent_extension {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ closure U ⊆ V ∧
      AnalyticOnNhd ℂ g V ∧ EqOn g f U ∧ InjOn g V ∧
      (∀ p ∈ frontier U, ‖g p‖ = 1) := by
  obtain ⟨V, g, hV, hUV, hga, hgf, hgd, hfront⟩ :=
    exists_extension_to_closure hU hf hbij hchart
  have hbijg : BijOn g U (ball 0 1) := hbij.congr hgf.symm
  have hgi := injOn_closure_of_boundary_modulus hU hUV hga hbijg hgd hfront
  have hloc : ∀ x ∈ closure U, ∃ s ∈ 𝓝 x, InjOn g s := by
    intro x hx
    let d := (hga x (hUV hx)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hgd x hx)
    let e := d.toOpenPartialHomeomorph g
    have he : x ∈ e.source := d.mem_toOpenPartialHomeomorph_source
    exact ⟨e.source, e.open_source.mem_nhds he, e.injOn⟩
  obtain ⟨W, hW, hUW, hgiW⟩ := hgi.exists_isOpen_superset hb.isCompact_closure
    (fun x hx => (hga x (hUV hx)).continuousAt) hloc
  exact ⟨V ∩ W, g, hV.inter hW, subset_inter hUV hUW,
    hga.mono inter_subset_left, hgf, hgiW.mono inter_subset_right, hfront⟩

end CrouzeixHilbert.Conformal

end

end OAI
