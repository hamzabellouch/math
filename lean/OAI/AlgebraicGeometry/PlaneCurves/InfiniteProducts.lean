import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace OAI

/-!
# Uniform estimates and limits for infinite products
-/

section

/-! Finite products and powers preserve locally uniform convergence to one.
These facts combine the individual normalized theta factors in §03. -/
noncomputable section
open Filter Topology

namespace Nagata.W03

variable {α β R : Type*} [TopologicalSpace β] [NormedCommRing R]
  {l : Filter α} {s : Set β}

/-- A constant family of functions with value one converges locally uniformly. -/
theorem tendstoLocallyUniformlyOn_const_one :
    TendstoLocallyUniformlyOn (fun _ : α => fun _ : β => (1 : R))
      (fun _ => 1) l s :=
  (tendsto_const_nhds.tendstoUniformlyOn_const s).tendstoLocallyUniformlyOn

/-- A fixed natural power of a family converging locally uniformly to one has
the same limit. No pointwise differentiability premise is needed. -/
theorem tendstoLocallyUniformlyOn_pow_one {F : α → β → R}
    (hF : TendstoLocallyUniformlyOn F (fun _ => 1) l s) (c : ℕ) :
    TendstoLocallyUniformlyOn (fun a x => F a x ^ c) (fun _ => 1) l s := by
  induction c with
  | zero => simpa using (tendstoLocallyUniformlyOn_const_one (R := R) (l := l) (s := s))
  | succ c ih =>
    simpa only [pow_succ, Pi.mul_def, one_mul] using
      ih.mul₀ hF continuousOn_const continuousOn_const

/-- Every finite product of families tending locally uniformly to one tends
locally uniformly to one, including the empty product. -/
theorem tendstoLocallyUniformlyOn_finset_prod_one {ι : Type*}
    (T : Finset ι) {F : ι → α → β → R}
    (hF : ∀ i ∈ T, TendstoLocallyUniformlyOn (F i) (fun _ => 1) l s) :
    TendstoLocallyUniformlyOn (fun a x => ∏ i ∈ T, F i a x) (fun _ => 1) l s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using (tendstoLocallyUniformlyOn_const_one (R := R) (l := l) (s := s))
  | @insert i T hi ih =>
    have hFi := hF i (Finset.mem_insert_self i T)
    have hFT : ∀ j ∈ T, TendstoLocallyUniformlyOn (F j) (fun _ => 1) l s :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.prod_insert hi, Pi.mul_def, one_mul] using
      hFi.mul₀ (ih hFT) continuousOn_const continuousOn_const

/-- Fintype form, convenient for the nine marked-point factors. -/
theorem tendstoLocallyUniformlyOn_fintype_prod_one {ι : Type*} [Fintype ι]
    {F : ι → α → β → R}
    (hF : ∀ i, TendstoLocallyUniformlyOn (F i) (fun _ => 1) l s) :
    TendstoLocallyUniformlyOn (fun a x => ∏ i, F i a x) (fun _ => 1) l s :=
  tendstoLocallyUniformlyOn_finset_prod_one Finset.univ (fun i _ => hF i)

end Nagata.W03

end
end

section

/-!
# Quantitative convergence of products close to one
-/
noncomputable section
open Filter Topology

namespace Nagata.W03

/-- Infinite-product version of the finite product estimate. -/
theorem norm_tprod_one_add_sub_one_le {ι R : Type*}
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {u : ι → R} (hu : Summable (fun i => ‖u i‖)) :
    ‖(∏' i, (1 + u i)) - 1‖ ≤ Real.exp (∑' i, ‖u i‖) - 1 := by
  have hp : Tendsto (fun t : Finset ι => ∏ i ∈ t, (1 + u i)) atTop
      (𝓝 (∏' i, (1 + u i))) := (multipliable_one_add_of_summable hu).hasProd
  have hs : Tendsto (fun t : Finset ι => ∑ i ∈ t, ‖u i‖) atTop
      (𝓝 (∑' i, ‖u i‖)) := hu.hasSum
  have hl := (hp.sub (tendsto_const_nhds (x := (1 : R)))).norm
  have hr := ((Real.continuous_exp.tendsto _).comp hs).sub (tendsto_const_nhds (x := (1 : ℝ)))
  exact le_of_tendsto_of_tendsto' hl hr (fun t => t.norm_prod_one_add_sub_one_le u)

/-- A scalar upper bound on the norm sum bounds the infinite product's error. -/
theorem norm_tprod_one_add_sub_one_le_of_tsum_norm_le {ι R : Type*}
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {u : ι → R} {B : ℝ} (hu : Summable (fun i => ‖u i‖))
    (hB : (∑' i, ‖u i‖) ≤ B) :
    ‖(∏' i, (1 + u i)) - 1‖ ≤ Real.exp B - 1 :=
  (norm_tprod_one_add_sub_one_le hu).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hB) 1)

/-- Uniform vanishing of a scalar bound on total norms makes the actual products
converge uniformly to one. Summability and bounds need hold only eventually. -/
theorem tendstoUniformlyOn_tprod_one_add_of_tsum_norm_le
    {α β ι R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {l : Filter α} {s : Set β} {u : α → ι → β → R} {B : α → ℝ}
    (hB : Tendsto B l (𝓝 0))
    (hsum : ∀ᶠ a in l, ∀ x ∈ s, Summable (fun i => ‖u a i x‖))
    (hbound : ∀ᶠ a in l, ∀ x ∈ s, (∑' i, ‖u a i x‖) ≤ B a) :
    TendstoUniformlyOn (fun a x => ∏' i, (1 + u a i x)) (fun _ => 1) l s := by
  have hlim : Tendsto (fun a => Real.exp (B a) - 1) l (𝓝 0) := by
    simpa using ((Real.continuous_exp.tendsto 0).comp hB).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ a in l, Real.exp (B a) - 1 < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hsum, hbound, hsmall] with a hs hb he x hx
  have hnorm := (norm_tprod_one_add_sub_one_le_of_tsum_norm_le
    (hs x hx) (hb x hx)).trans_lt he
  simpa only [dist_eq_norm, norm_sub_rev] using hnorm

/-- Local bounds may use a different scalar majorant on each neighbourhood. -/
theorem tendstoLocallyUniformlyOn_tprod_one_add_of_local_tsum_norm_le
    {α β ι R : Type*} [TopologicalSpace β]
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {l : Filter α} {s : Set β} {u : α → ι → β → R}
    (hlocal : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∃ B : α → ℝ,
      Tendsto B l (𝓝 0) ∧
      (∀ᶠ a in l, ∀ y ∈ t, Summable (fun i => ‖u a i y‖)) ∧
      (∀ᶠ a in l, ∀ y ∈ t, (∑' i, ‖u a i y‖) ≤ B a)) :
    TendstoLocallyUniformlyOn (fun a x => ∏' i, (1 + u a i x))
      (fun _ => 1) l s := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨t, ht, B, hB, hsum, hbound⟩ := hlocal x hx
  exact ⟨t, ht, tendstoUniformlyOn_tprod_one_add_of_tsum_norm_le hB hsum hbound⟩

/-- On an open locally compact domain it suffices to give vanishing majorants
on every compact subset; this is the usual analytic local-uniform formulation. -/
theorem tendstoLocallyUniformlyOn_tprod_one_add_of_compact_tsum_norm_le
    {α β ι R : Type*} [TopologicalSpace β] [LocallyCompactSpace β]
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {l : Filter α} {s : Set β} {u : α → ι → β → R} (hs : IsOpen s)
    (hcompact : ∀ K : Set β, K ⊆ s → IsCompact K → ∃ B : α → ℝ,
      Tendsto B l (𝓝 0) ∧
      (∀ᶠ a in l, ∀ x ∈ K, Summable (fun i => ‖u a i x‖)) ∧
      (∀ᶠ a in l, ∀ x ∈ K, (∑' i, ‖u a i x‖) ≤ B a)) :
    TendstoLocallyUniformlyOn (fun a x => ∏' i, (1 + u a i x))
      (fun _ => 1) l s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hKs hK
  obtain ⟨B, hB, hsum, hbound⟩ := hcompact K hKs hK
  exact tendstoUniformlyOn_tprod_one_add_of_tsum_norm_le hB hsum hbound

end Nagata.W03

end
end

end OAI
