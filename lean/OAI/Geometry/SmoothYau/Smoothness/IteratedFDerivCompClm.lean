import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma iteratedFDeriv_comp_clm_at (L : F →L[ℝ] E) {f : E → G} {x : F} (n : ℕ)
    (hf : ContDiffAt ℝ n f (L x)) :
    iteratedFDeriv ℝ n (f ∘ L) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hVo,hx⟩ := mem_nhds_iff.mp hU
  have he := L.iteratedFDerivWithin_comp_right (hu.mono hVU) hVo.uniqueDiffOn
    (hVo.preimage L.continuous).uniqueDiffOn hx (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen n hVo hx,
    iteratedFDerivWithin_of_isOpen n (hVo.preimage L.continuous) hx] at he
  exact he

lemma partial_iteratedFDeriv (f : ℝ × E → F) (t : ℝ) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f (t,x)) :
    iteratedFDeriv ℝ n (fun y => f (t,y)) x =
      (iteratedFDeriv ℝ n f (t,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  let q : ℝ × E → F := fun z => f ((t,0)+z)
  have hq : ContDiffAt ℝ n q (L x) := by
    have hg : ContDiffAt ℝ n (fun z : ℝ × E => (t,0)+z) (L x) := by fun_prop
    exact (show ContDiffAt ℝ n f ((t,0)+L x) by simpa [L] using hf).comp (L x) hg
  have hj := iteratedFDeriv_comp_clm_at L n hq
  simpa [q,L,Function.comp_def,iteratedFDeriv_comp_add_left] using hj

lemma continuousAt_partial_iteratedFDeriv (f : ℝ × E → F) {z : ℝ × E} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f z) :
    ContinuousAt (fun w : ℝ × E => iteratedFDeriv ℝ n (fun y => f (w.1,y)) w.2) z := by
  have hc := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ E)).continuousAt.comp
      (hf.continuousAt_iteratedFDeriv (k := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hf.of_le (show (n : WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).eventually (by simp)] with w hw
  exact partial_iteratedFDeriv f w.1 w.2 n hw

theorem compact_parameter_jets {f : ℝ × E → F} {K : Set E} (hK : IsCompact K)
    {t₀ : ℝ} (hf : ∀ y ∈ K, ContDiffAt ℝ ∞ f (t₀,y)) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ n (fun z => f (t,z) - f (t₀,z)) y‖ < ε := by
  have hj := hK.eventually_forall_of_forall_eventually (x₀ := t₀)
    (P := fun t y => ContDiffAt ℝ n f (t,y) ∧
      ‖iteratedFDeriv ℝ n (fun z => f (t,z)) y -
        iteratedFDeriv ℝ n (fun z => f (t₀,z)) y‖ < ε) (fun y hy => ?_)
  · filter_upwards [hj] with t ht y hy
    have h0 := ((hf y hy).of_le (show (n : WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
    have hft := (ht y hy).1.comp y (contDiffAt_const.prodMk contDiffAt_id)
    change ‖iteratedFDeriv ℝ n ((f ∘ Prod.mk t) - (f ∘ Prod.mk t₀)) y‖ < ε
    rw [iteratedFDeriv_sub_apply hft h0]
    exact (ht y hy).2
  · have h1 := continuousAt_partial_iteratedFDeriv f n (hf y hy)
    have h0 := (hf y hy).comp y (contDiffAt_const.prodMk contDiffAt_id)
    have h2 := (h0.continuousAt_iteratedFDeriv (k:=n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp (continuousAt_snd : ContinuousAt (fun w : ℝ × E => w.2) (t₀,y))
    have hh := (h1.sub h2).norm
    have he : ∀ᶠ w : ℝ × E in 𝓝 (t₀,y),
        ‖iteratedFDeriv ℝ n (fun z => f (w.1,z)) w.2 -
          iteratedFDeriv ℝ n (fun z => f (t₀,z)) w.2‖ < ε :=
      hh.eventually (gt_mem_nhds (by simpa [Function.comp_def] using hε))
    exact ((hf y hy).of_le (show (n : WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).eventually (by simp) |>.and he
end YauCounterexamples

end

end OAI
