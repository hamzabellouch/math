import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicOffsetLimits

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
namespace Release061
open Set Filter Metric MeasureTheory Topology

theorem semialgebraic_selection_analytic_path {n k : ℕ}
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (v : (Fin (n+1) → ℝ) → (Fin k → ℝ))
    (hgraph : ∀ j, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = v (fun i => x (some i)) j})
    (hselect : ∀ x : Fin (n+1) → ℝ, Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε →
      v x ∈ A (Fin.tail x) ∧ ‖v x‖ < x 0) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ η > 0,
        ∃ ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ),
          ball s r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 η) ∧
          (∀ x ∈ ball s r, ψ (x,0) = 0) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η, ψ (x,t) ∈ A x := by
  have hbound : ∀ j (x : Fin (n+1) → ℝ), Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε →
      ‖v x j‖ ≤ ε := by
    intro j x hx ht
    exact ((norm_le_pi_norm (v x) j).trans_lt ((hselect x hx ht).2.trans ht.2)).le
  obtain ⟨E,hEB,hE,hg⟩ := finite_semialgebraic_ramification hB hε
    (fun j x => v x j) hgraph (fun _ => ε) hbound
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  obtain ⟨r,hr,L,hL,η,hη,F,hrB,hFa,hF⟩ := hg s hs hsE
  let δ := min η (min ε 1)
  have hδ : 0 < δ := lt_min hη (lt_min hε zero_lt_one)
  have hδη : δ ≤ η := min_le_left _ _
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  let ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ) := fun p j => F j p
  have hψa : AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 δ) := by
    intro p hp
    apply analyticAt_pi_iff.mpr
    intro j
    exact hFa j p ⟨hp.1,ball_subset_ball hδη hp.2⟩
  have huL : ∀ u ∈ Ioo (0 : ℝ) δ, u^L ∈ Ioo (0 : ℝ) ε ∧ u^L ≤ u := by
    intro u hu
    have hh := pow_le_of_le_one hu.1.le (hu.2.le.trans hδ1) hL.ne'
    exact ⟨⟨pow_pos hu.1 _,hh.trans_lt (hu.2.trans_le hδε)⟩,hh⟩
  have hψ : ∀ x ∈ ball s r, ∀ u ∈ Ioo (0 : ℝ) δ,
      ψ (x,u) = v (Fin.cons (u^L) x) := by
    intro x hx u hu
    funext j
    exact hF j x hx u ⟨hu.1,hu.2.trans_le hδη⟩
  have hstep : ∀ x ∈ ball s r, ∀ u ∈ Ioo (0 : ℝ) δ,
      ψ (x,u) ∈ A x ∧ ‖ψ (x,u)‖ ≤ u := by
    intro x hx u hu
    have h := hselect (Fin.cons (u^L) x) (by simpa only [Fin.tail_cons] using hrB hx)
      (by simpa only [Fin.cons_zero] using (huL u hu).1)
    rw [hψ x hx u hu]
    exact ⟨by simpa only [Fin.tail_cons] using h.1,h.2.le.trans (huL u hu).2⟩
  refine ⟨r,hr,δ,hδ,ψ,hrB,hψa,?_,fun x hx u hu => (hstep x hx u hu).1⟩
  intro x hx
  have hc : Tendsto (fun u : ℝ => ψ (x,u)) (𝓝[>] (0 : ℝ)) (𝓝 (ψ (x,0))) :=
    (hψa (x,0) ⟨hx,mem_ball_self hδ⟩).continuousAt.tendsto.comp
      (tendsto_const_nhds.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds))
  have hz : Tendsto (fun u : ℝ => ψ (x,u)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun u => u) _ (tendsto_id.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT hδ] with u hu
    exact (hstep x hx u hu).2
  exact tendsto_nhds_unique hc hz

end Release061

end

end OAI
