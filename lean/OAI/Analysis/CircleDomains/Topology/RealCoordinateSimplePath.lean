import Mathlib.Topology.Path
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith

namespace OAI

/-! A continuous real coordinate with exactly the same fibers as a path
reparametrizes that path injectively on the unit interval. -/
open Set Function
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma simplePath_of_real_coordinate {X : Type*} [TopologicalSpace X]
    (g : C(unitInterval, X)) (q : C(unitInterval, ℝ)) (hqmono : Monotone q)
    (hfibers : ∀ s t, q s = q t ↔ g s = g t) (hne : g 0 ≠ g 1) :
    ∃ β : Path (g 0) (g 1), Injective β ∧ range β ⊆ range g := by
  let e : unitInterval → range q := fun t => ⟨q t, mem_range_self t⟩
  have he : Continuous e := q.continuous.subtype_mk _
  have hes : Surjective e := by
    rintro ⟨x, t, rfl⟩
    exact ⟨t, rfl⟩
  let r : range q → unitInterval := fun z => Classical.choose z.property
  have hr (z : range q) : q (r z) = z := Classical.choose_spec z.property
  let α : range q → X := fun z => g (r z)
  have hαe : α ∘ e = g := by
    funext t
    apply (hfibers _ _).mp
    exact hr (e t)
  have hα : Continuous α :=
    (Topology.IsQuotientMap.of_surjective_continuous hes he).continuous_iff.mpr
      (hαe ▸ g.continuous)
  have hαinj : Injective α := by
    intro z w h
    apply Subtype.ext
    exact (hr z).symm.trans (((hfibers _ _).mpr h).trans (hr w))
  have hq : q 0 < q 1 := lt_of_le_of_ne (hqmono bot_le)
    (fun h => hne ((hfibers 0 1).mp h))
  have hqr : Icc (q 0) (q 1) ⊆ range q :=
    (intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from bot_le)
      q.continuous.continuousOn).trans (image_subset_range _ _)
  let p : unitInterval → range q := fun t =>
    ⟨q 0 + (q 1 - q 0) * (t : ℝ), hqr (by
      have ht₀ := t.property.1
      have ht₁ := t.property.2
      constructor <;> nlinarith)⟩
  have hp : Continuous p :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _
  have hp0 : (p 0 : ℝ) = q 0 := by simp [p]
  have hp1 : (p 1 : ℝ) = q 1 := by simp [p]
  have hpinj : Injective p := by
    intro s t h
    have hv := congrArg Subtype.val h
    change q 0 + (q 1 - q 0) * (s : ℝ) = q 0 + (q 1 - q 0) * (t : ℝ) at hv
    apply Subtype.ext
    nlinarith
  let β : Path (g 0) (g 1) :=
    { toFun := fun t => α (p t)
      continuous_toFun := hα.comp hp
      source' := (hfibers _ _).mp ((hr (p 0)).trans hp0)
      target' := (hfibers _ _).mp ((hr (p 1)).trans hp1) }
  refine ⟨β, hαinj.comp hpinj, ?_⟩
  rintro z ⟨t, rfl⟩
  exact ⟨r (p t), rfl⟩

end CircleDomainRigidity

end

end OAI
