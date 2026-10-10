import OAI.NumberTheory.DukePrimeDegree.Geometry.ControlledRadialHeight
import OAI.NumberTheory.DukePrimeDegree.Entropy.ContractingCutItineraries

namespace OAI

/-! # Local constancy of controlled radial heights

Only the adjacent radial cuts determine the height. Avoiding all cuts up
to the current height therefore makes the entire height itinerary locally
constant along uniformly contracting perturbations.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree

lemma cut_le_agrees_of_abs_sub_le {u v r ε : ℝ}
    (hnear : |u-v| ≤ ε) (haway : ε < |v-r|) :
    (u ≤ r ↔ v ≤ r) := by
  have hn := abs_le.mp hnear
  by_cases hvr : v ≤ r
  · rw [abs_of_nonpos (sub_nonpos.mpr hvr)] at haway
    have hur : u ≤ r := by linarith
    exact iff_of_true hur hvr
  · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hvr))] at haway
    have hur : ¬ u ≤ r := by linarith
    exact iff_of_false hur hvr

lemma height_eq_of_threshold_agreement {Y : Type*}
    (H : Y → ℕ) (f : Y → ℝ) (t : ℕ → ℝ)
    (hlevel : ∀ y m, H y ≤ m ↔ f y ≤ t m) {x y : Y}
    (heq : ∀ m ≤ H x, f y ≤ t m ↔ f x ≤ t m) : H y=H x := by
  apply le_antisymm
  · exact (hlevel y (H x)).mpr ((heq _ le_rfl).mpr ((hlevel x _).mp le_rfl))
  · by_cases hx : H x=0
    · omega
    · have hprev : ¬ f x ≤ t (H x-1) := by
        intro h
        have := (hlevel x _).mpr h
        omega
      have hy : ¬ H y ≤ H x-1 := by
        intro h
        exact hprev ((heq _ (Nat.sub_le _ _)).mp ((hlevel y _).mp h))
      omega

lemma eventually_radial_height_eq {Y : Type*} [TopologicalSpace Y]
    (H : Y → ℕ) (f : Y → ℝ) (t : ℕ → ℝ)
    (hlevel : ∀ y m, H y ≤ m ↔ f y ≤ t m) {x : Y}
    (hf : ContinuousAt f x) (hboundary : ∀ m, f x≠t m) :
    ∀ᶠ y in 𝓝 x, H y=H x := by
  have hfinite (m : Fin (H x+1)) :
      ∀ᶠ y in 𝓝 x, f y ≤ t m.val ↔ f x ≤ t m.val := by
    rcases lt_or_gt_of_ne (hboundary m.val) with hlt | hgt
    · exact (hf.eventually (gt_mem_nhds hlt)).mono fun y hy => iff_of_true hy.le hlt.le
    · exact (hf.eventually (lt_mem_nhds hgt)).mono fun y hy =>
        iff_of_false (not_le.mpr hy) (not_le.mpr hgt)
  filter_upwards [Filter.eventually_all.mpr hfinite] with y hy
  apply height_eq_of_threshold_agreement H f t hlevel
  intro m hm
  exact hy ⟨m,by omega⟩

theorem eventually_radial_height_itinerary_eq
    {Y V : Type*} [TopologicalSpace Y] [TopologicalSpace V]
    {T : Y → Y} (hT : Continuous T) (H : Y → ℕ) (f : Y → ℝ) (t : ℕ → ℝ)
    (hlevel : ∀ y m, H y ≤ m ↔ f y ≤ t m) (hf : Continuous f)
    {F : V → Y} {v₀ : V} (hF : ContinuousAt F v₀)
    (ε : ℕ → ℝ)
    (hboundary : ∀ k m, f (T^[k] (F v₀))≠t m)
    (havoid : ∀ᶠ k : ℕ in atTop, ∀ m ≤ H (T^[k] (F v₀)),
      ε k < |f (T^[k] (F v₀))-t m|)
    (U : Set V) (hU : U ∈ 𝓝 v₀)
    (hcontract : ∀ k : ℕ, ∀ v ∈ U,
      |f (T^[k] (F v))-f (T^[k] (F v₀))| ≤ ε k) :
    ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ, H (T^[k] (F v))=H (T^[k] (F v₀)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp havoid
  have hfinite (k : Fin N) : ∀ᶠ v in 𝓝 v₀,
      H (T^[k.val] (F v))=H (T^[k.val] (F v₀)) := by
    have hcont : ContinuousAt (fun v => T^[k.val] (F v)) v₀ :=
      (hT.iterate k.val).continuousAt.comp hF
    exact hcont.eventually (eventually_radial_height_eq H f t hlevel
      hf.continuousAt (hboundary k.val))
  filter_upwards [Filter.eventually_all.mpr hfinite,hU] with v hv hvU
  intro k
  by_cases hk : k < N
  · exact hv ⟨k,hk⟩
  · apply height_eq_of_threshold_agreement H f t hlevel
    intro m hm
    exact cut_le_agrees_of_abs_sub_le (hcontract k v hvU)
      (hN k (le_of_not_gt hk) m hm)

end DukePrimeDegree

end

end OAI
