import OAI.NumberTheory.Jacobsthal.Harmonic.PolynomialLocalGraph

namespace OAI

namespace Erdos970

section

open Filter Set
open scoped Topology ContDiff
namespace ErdosLocalFiberGraphs
open ErdosImplicitCurvature ErdosDivisibleInflection

theorem exists_local_graph_iff (Q : Bivariate) (x y : ℝ)
    (hQ : peval Q x y = 0) (hQy : peval (partialY Q) x y ≠ 0)
    (V : Set ℝ) (hV : IsOpen V) (hyV : y ∈ V) :
    ∃ (a b : ℝ) (W : Set ℝ) (f : ℝ → ℝ),
      a < x ∧ x < b ∧ IsOpen W ∧ y ∈ W ∧ W ⊆ V ∧ f x = y ∧
      ContDiffOn ℝ 2 f (Ioo a b) ∧
      (∀ t ∈ Ioo a b, f t ∈ W) ∧
      (∀ t ∈ Ioo a b, peval (partialY Q) t (f t) ≠ 0) ∧
      (∀ t ∈ Ioo a b, ∀ z ∈ W, peval Q t z = 0 ↔ z = f t) := by
  have hc : ContDiffAt ℝ 2 (planeEval Q) (x,y) := (contDiff_planeEval Q 2).contDiffAt
  have hi : (fderiv ℝ (planeEval Q) (x,y) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [fderiv_planeEval_inr]
    exact scalar_map_invertible _ hQy
  let f := hc.implicitFunction (by norm_num) hi
  have hfx : f x = y := hc.implicitFunction_apply_self (by norm_num) hi
  have hcf : ContDiffAt ℝ 2 f x := hc.contDiffAt_implicitFunction (by norm_num) hi
  have heq : ∀ᶠ v in 𝓝 (x,y), peval Q v.1 v.2 = 0 ↔ v.2 = f v.1 := by
    have h := hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi
    exact h.mono fun v hv => by simpa only [planeEval, hQ, eq_comm] using hv
  obtain ⟨U,V₀,hU,hxU,hV₀,hyV₀,hUV⟩ := mem_nhds_prod_iff'.mp heq
  let W := V ∩ V₀
  have hW : IsOpen W := hV.inter hV₀
  have hyW : y ∈ W := ⟨hyV,hyV₀⟩
  have hmem : ∀ᶠ t in 𝓝 x, f t ∈ W :=
    hcf.continuousAt.preimage_mem_nhds (hfx ▸ hW.mem_nhds hyW)
  have hpair : ContinuousAt (fun t : ℝ => (t,f t)) x :=
    continuousAt_id.prodMk hcf.continuousAt
  have hplane : ContinuousAt (planeEval (partialY Q)) (x,f x) :=
    (contDiff_planeEval (partialY Q) 0).continuous.continuousAt
  have hcy : ContinuousAt (fun t => peval (partialY Q) t (f t)) x := by
    change ContinuousAt (planeEval (partialY Q) ∘ (fun t : ℝ => (t,f t))) x
    exact ContinuousAt.comp (f := fun t : ℝ => (t,f t)) hplane hpair
  have hny : ∀ᶠ t in 𝓝 x, peval (partialY Q) t (f t) ≠ 0 := by
    apply hcy.eventually_ne
    rwa [hfx]
  obtain ⟨D,hD,hfD⟩ := hcf.contDiffOn (m := 2) le_rfl (by norm_num)
  have hN : U ∩ D ∩ {t | f t ∈ W} ∩ {t | peval (partialY Q) t (f t) ≠ 0} ∈ 𝓝 x :=
    inter_mem (inter_mem (inter_mem (hU.mem_nhds hxU) hD) hmem) hny
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hN
  have hs : Ioo (x-eps) (x+eps) ⊆
      U ∩ D ∩ {t | f t ∈ W} ∩ {t | peval (partialY Q) t (f t) ≠ 0} := by
    simpa only [Real.ball_eq_Ioo] using hball
  refine ⟨x-eps,x+eps,W,f,by linarith,by linarith,hW,hyW,
    inter_subset_left,hfx,hfD.mono (fun t ht => (hs ht).1.1.2),
    (fun t ht => (hs ht).1.2),(fun t ht => (hs ht).2),?_⟩
  intro t ht z hz
  exact hUV (a := (t,z)) ⟨(hs ht).1.1.1,hz.2⟩

end ErdosLocalFiberGraphs

end

end Erdos970

end OAI
