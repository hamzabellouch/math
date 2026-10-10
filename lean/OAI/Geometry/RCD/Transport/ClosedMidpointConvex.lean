import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact

namespace OAI

/-! # Closed midpoint sets and the local distance-coordinate image -/

open Set
noncomputable section
namespace RegularPointCoordinates

theorem closed_midpoints_fill_interval {s : Set ℝ} (hs : IsClosed s)
    (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hm : ∀ x ∈ s, ∀ y ∈ s, (x+y)/2 ∈ s) : Icc (0:ℝ) 1 ⊆ s := by
  intro t ht
  have hL : IsCompact (s ∩ Icc 0 t) := isCompact_Icc.inter_left hs
  have hR : IsCompact (s ∩ Icc t 1) := isCompact_Icc.inter_left hs
  obtain ⟨l,hl,hmax⟩ := hL.exists_isMaxOn ⟨0,h0,le_rfl,ht.1⟩ continuous_id.continuousOn
  obtain ⟨u,hu,hmin⟩ := hR.exists_isMinOn ⟨1,h1,ht.2,le_rfl⟩ continuous_id.continuousOn
  have hmid := hm l hl.1 u hu.1
  have hlu : l ≤ u := hl.2.2.trans hu.2.1
  have heq : l = u := by
    by_cases hmt : (l+u)/2 ≤ t
    · have hh := hmax ⟨hmid,by linarith [hl.2.1,hu.2.1],hmt⟩
      change (l+u)/2 ≤ l at hh
      linarith
    · have hh := hmin ⟨hmid,by linarith,by linarith [hl.2.2,hu.2.2]⟩
      change u ≤ (l+u)/2 at hh
      linarith
  have hlt : l = t := by linarith [hl.2.2,hu.2.1]
  exact hlt ▸ hl.1

theorem isClosed_convex_of_midpoints {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {s : Set E} (hs : IsClosed s)
    (hm : ∀ x ∈ s, ∀ y ∈ s, (1/2:ℝ) • (x+y) ∈ s) : Convex ℝ s := by
  apply convex_iff_add_mem.mpr
  intro x hx y hy a b ha hb hab
  let f (t : ℝ) := (1-t) • x+t • y
  have hf : Continuous f := by fun_prop
  have h0 : (0:ℝ) ∈ f ⁻¹' s := by simpa only [mem_preimage,f,sub_zero,one_smul,zero_smul,add_zero] using hx
  have h1 : (1:ℝ) ∈ f ⁻¹' s := by simpa only [mem_preimage,f,sub_self,zero_smul,one_smul,zero_add] using hy
  have hmid : ∀ t ∈ f ⁻¹' s, ∀ u ∈ f ⁻¹' s, (t+u)/2 ∈ f ⁻¹' s := by
    intro t ht u hu
    change f ((t+u)/2) ∈ s
    have he : f ((t+u)/2) = (1/2:ℝ) • (f t+f u) := by
      dsimp only [f]
      module
    rw [he]
    exact hm _ ht _ hu
  have hh := closed_midpoints_fill_interval (hs.preimage hf) h0 h1 hmid
    (show b ∈ Icc (0:ℝ) 1 from ⟨hb,by linarith⟩)
  change (1-b) • x+b • y ∈ s at hh
  rwa [show 1-b=a by linarith] at hh

end RegularPointCoordinates

end

end OAI
