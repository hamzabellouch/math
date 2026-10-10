import OAI.NumberTheory.DukePrimeDegree.Geometry.RadialHeightContinuity

namespace OAI

/-! # Locally constant future cuts at a varying height -/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree

theorem eventually_varying_cut_itinerary_eq
    {Y V : Type*} [TopologicalSpace Y] [TopologicalSpace V]
    {T : Y → Y} (hT : Continuous T) (H : Y → ℕ)
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Continuous (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    {F : V → Y} {v₀ : V} (hF : ContinuousAt F v₀)
    (ε : ℕ → ℝ)
    (hboundary : ∀ k m i, f m i (T^[k] (F v₀))≠c m i)
    (havoid : ∀ᶠ k : ℕ in atTop, ∀ m ≤ H (T^[k] (F v₀)), ∀ i,
      ε k < |f m i (T^[k] (F v₀))-c m i|)
    (U : Set V) (hU : U ∈ 𝓝 v₀)
    (hcontract : ∀ k m i, ∀ v ∈ U,
      |f m i (T^[k] (F v))-f m i (T^[k] (F v₀))| ≤ ε k) :
    ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ, ∀ i : Fin (N (H (T^[k] (F v₀)))),
      f (H (T^[k] (F v₀))) i (T^[k] (F v)) < c (H (T^[k] (F v₀))) i ↔
        f (H (T^[k] (F v₀))) i (T^[k] (F v₀)) < c (H (T^[k] (F v₀))) i := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp havoid
  have hfinite (k : Fin M) : ∀ᶠ v in 𝓝 v₀,
      ∀ i : Fin (N (H (T^[k.val] (F v₀)))),
      f (H (T^[k.val] (F v₀))) i (T^[k.val] (F v)) < c (H (T^[k.val] (F v₀))) i ↔
        f (H (T^[k.val] (F v₀))) i (T^[k.val] (F v₀)) < c (H (T^[k.val] (F v₀))) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt
        (fun v => f (H (T^[k.val] (F v₀))) i (T^[k.val] (F v))) v₀ :=
      ((hf _ _).comp (hT.iterate k.val)).continuousAt.comp hF
    rcases lt_or_gt_of_ne (hboundary k.val _ i) with hlt | hgt
    · exact (hc.eventually (gt_mem_nhds hlt)).mono fun _ hv => iff_of_true hv hlt
    · exact (hc.eventually (lt_mem_nhds hgt)).mono fun _ hv =>
        iff_of_false (not_lt.mpr hv.le) (not_lt.mpr hgt.le)
  filter_upwards [Filter.eventually_all.mpr hfinite,hU] with v hv hvU
  intro k i
  by_cases hk : k < M
  · exact hv ⟨k,hk⟩ i
  · exact cut_agrees_of_abs_sub_le (hcontract k _ i v hvU)
      (hM k (le_of_not_gt hk) _ le_rfl i)

end DukePrimeDegree

end

end OAI
