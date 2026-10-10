import OAI.Probability.DilutedSpin.BoundedCavityLower
import OAI.Probability.DilutedSpin.ClippedModelFacts
import OAI.Probability.DilutedSpin.FunctionalStability
import OAI.Probability.DilutedSpin.PressureLiminf

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

lemma symmetric_trial_lower {q : ℕ} (M : Model (q+1)) (hα : 0 < M.alpha)
    (hθ : Integrable (fun z : InteractionSample (q+1) => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ),Exponents m ∧
      functional M r ζ m ≤ liminf (pressure M) atTop+ε := by
  let D := fun K : ℕ => ∫ z : InteractionSample (q+1),‖(clipSample (K:ℝ) z).1-z.1‖ ∂M.disorder.toMeasure
  let d := fun K : ℕ => ∫ h : ℝ,|clipReal (K:ℝ) h-h| ∂M.field.toMeasure
  have hD : Tendsto D atTop (𝓝 0) := by simpa only [D,norm_sub_rev] using clipping_interaction_error_tendsto M hθ
  have hd : Tendsto d atTop (𝓝 0) := by simpa only [d,abs_sub_comm] using clipping_field_error_tendsto M hh
  have he : Tendsto (fun K => (M.alpha:ℝ)*((q+1:ℕ)+(q:ℝ)+1)*D K+2*d K) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (hD.const_mul ((M.alpha:ℝ)*((q+1:ℕ)+(q:ℝ)+1))).add (hd.const_mul 2)
  obtain ⟨K,hK⟩ := ((tendsto_order.1 he).2 (ε/2) (by positivity)).exists
  have hK0 : 0 ≤ (K:ℝ) := Nat.cast_nonneg K
  obtain ⟨r,ζ,m,hm,hl⟩ := UniversalDictionary.bounded_symmetric_trial_lower (clippedModel M (K:ℝ)) hα hK0 hK0
    (clippedModel_interaction_bounded M hK0) (clippedModel_field_bounded M hK0)
    (clippedModel_interaction_integrable M hK0) (clippedModel_field_integrable M hK0)
    (clippedModel_symmetric M (K:ℝ) hsym) (show 0 < ε/2 by positivity)
  have hDi := clip_interaction_difference_integrable M hK0 hθ
  have hdi := clip_field_difference_integrable M hK0 hh
  have hP : liminf (pressure (clippedModel M (K:ℝ))) atTop ≤ liminf (pressure M) atTop+(M.alpha:ℝ)*D K+d K := by
    have he' : ∀ᶠ N in atTop,pressure (clippedModel M (K:ℝ)) N ≤ pressure M N+((M.alpha:ℝ)*D K+d K) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hb := (abs_le.mp (pressure_map_stability M hN hθ hh (clipSample (K:ℝ)) (clipReal (K:ℝ))
        (measurable_clipSample _) (measurable_clipReal _) hDi hdi)).2
      change pressure (clippedModel M (K:ℝ)) N-pressure M N ≤ (M.alpha:ℝ)*D K+d K at hb
      linarith
    have hb := liminf_le_liminf_add_of_eventually_le
      (pressure_bounded (clippedModel M (K:ℝ)) (clippedModel_interaction_integrable M hK0) (clippedModel_field_integrable M hK0)).2
      (pressure_bounded M hθ hh) he'
    linarith
  have hF := (abs_le.mp (functional_map_stability M m (fun i => (hm.2 i).1) ζ hθ hh
    (clipSample (K:ℝ)) (clipReal (K:ℝ)) (measurable_clipSample _) (measurable_clipReal _) hDi hdi)).1
  change -((M.alpha:ℝ)*(((q+1:ℕ):ℝ)+((q+1-1:ℕ):ℝ))*D K+d K) ≤
    functional (clippedModel M (K:ℝ)) r ζ m-functional M r ζ m at hF
  simp only [Nat.add_sub_cancel] at hF
  refine ⟨r,ζ,m,hm,?_⟩
  nlinarith
end DilutedSpinGlass

end

end OAI
