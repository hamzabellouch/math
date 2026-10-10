import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryBounds

namespace OAI

/-! A common compact spatial support controls all derivatives, including time
jets. Periodicity is used only to reduce the time variable to one closed cell. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set Filter
open scoped ContDiff Topology

theorem mixedDerivative_common_support {V : Velocity} {K : Set Space}
    (hK : IsClosed K) (hV : ∀ t, tsupport (fun x => V (t, x)) ⊆ K)
    (α : List (Fin 4)) (t : ℝ) :
    tsupport (fun x => mixedDerivative V α (t, x)) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have ho : {y : SpaceTime | y.2 ∉ K} ∈ 𝓝 (t, x) :=
    (hK.isOpen_compl.preimage continuous_snd).mem_nhds hn
  have he : V =ᶠ[𝓝 (t, x)] fun _ => 0 := by
    filter_upwards [ho] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := fun x : Space => V (y.1, x))
      (fun hm => hy (hV y.1 hm))
  have hz := (mixedDerivative_eventuallyEq he α).self_of_nhds
  rw [mixedDerivative_zero] at hz
  exact hx hz

theorem boundedMixed_of_compact_periodic {V : Velocity} {K : Set Space}
    (hV : ContDiff ℝ ∞ V) (hK : IsCompact K)
    (hs : ∀ t, tsupport (fun x => V (t, x)) ⊆ K) (hp : TimePeriodic V) :
    BoundedMixedDerivatives V := by
  intro α
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).bddAbove_image
    (mixedDerivative_smooth hV α).continuous.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  rintro ⟨t, x⟩
  by_cases hx : x ∈ K
  · have ht : Function.Periodic (fun s => mixedDerivative V α (s, x)) 1 :=
      fun s => mixedDerivative_time_periodic hV hp α s x
    have he : mixedDerivative V α (Int.fract t, x) = mixedDerivative V α (t, x) := by
      simpa only [Int.fract, mul_one] using ht.sub_int_mul_eq (x := t) ⌊t⌋
    rw [← he]
    exact (hC (mem_image_of_mem _
      (show (Int.fract t, x) ∈ Icc (0 : ℝ) 1 ×ˢ K from
        ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, hx⟩))).trans (le_max_left _ _)
  · have hz : mixedDerivative V α (t, x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x : Space => mixedDerivative V α (t, x))
        (fun hm => hx (mixedDerivative_common_support hK.isClosed hs α t hm))
    rw [hz, norm_zero]
    exact le_max_right _ _

theorem boundedMixed_of_compact_tail {F G : Velocity} {K : Set Space}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hK : IsCompact K)
    (hsF : ∀ t, tsupport (fun x => F (t, x)) ⊆ K)
    (hsG : ∀ t, tsupport (fun x => G (t, x)) ⊆ K) (hpG : TimePeriodic G)
    (hleft : ∀ t, t < 0 → ∀ x, F (t, x) = 0)
    (hright : ∀ t, 1 < t → ∀ x, F (t, x) = G (t, x)) :
    BoundedMixedDerivatives F := by
  intro α
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).bddAbove_image
    (mixedDerivative_smooth hF α).continuous.norm.continuousOn
  obtain ⟨D, hD, hbD⟩ := boundedMixed_of_compact_periodic hG hK hsG hpG α
  refine ⟨max C D, hD.trans (le_max_right _ _), ?_⟩
  rintro ⟨t, x⟩
  by_cases ht0 : t < 0
  · have he : F =ᶠ[𝓝 (t, x)] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto (t, x)).eventually (eventually_lt_nhds ht0)] with y hy
      exact hleft y.1 hy y.2
    rw [(mixedDerivative_eventuallyEq he α).self_of_nhds, mixedDerivative_zero, norm_zero]
    exact hD.trans (le_max_right _ _)
  by_cases ht1 : 1 < t
  · have he : F =ᶠ[𝓝 (t, x)] G := by
      filter_upwards [(continuous_fst.tendsto (t, x)).eventually (eventually_gt_nhds ht1)] with y hy
      exact hright y.1 hy y.2
    rw [(mixedDerivative_eventuallyEq he α).self_of_nhds]
    exact (hbD (t, x)).trans (le_max_right _ _)
  by_cases hx : x ∈ K
  · exact (hC (mem_image_of_mem _
      (show (t, x) ∈ Icc (0 : ℝ) 1 ×ˢ K from
        ⟨⟨le_of_not_gt ht0, le_of_not_gt ht1⟩, hx⟩))).trans (le_max_left _ _)
  · have hz : mixedDerivative F α (t, x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x : Space => mixedDerivative F α (t, x))
        (fun hm => hx (mixedDerivative_common_support hK.isClosed hsF α t hm))
    rw [hz, norm_zero]
    exact hD.trans (le_max_right _ _)

end ForcedComputation

end

end OAI
