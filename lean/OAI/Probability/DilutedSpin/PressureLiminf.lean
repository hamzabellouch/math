import OAI.Probability.DilutedSpin.FunctionalStability

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter

lemma pressure_bounded {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    IsBoundedUnder (· ≤ ·) atTop (pressure M) ∧ IsBoundedUnder (· ≥ ·) atTop (pressure M) := by
  have he : ∀ᶠ N in atTop, |pressure M N-Real.log 2| ≤ (M.alpha:ℝ)*interactionMoment M+fieldMoment M := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (disorderAverage_integrable_and_pressure_bound M hθ hh hN).2
  constructor
  · apply isBoundedUnder_of_eventually_le (a := Real.log 2+(M.alpha:ℝ)*interactionMoment M+fieldMoment M)
    filter_upwards [he] with N hN
    linarith [(abs_le.mp hN).2]
  · apply isBoundedUnder_of_eventually_ge (a := Real.log 2-((M.alpha:ℝ)*interactionMoment M+fieldMoment M))
    filter_upwards [he] with N hN
    linarith [(abs_le.mp hN).1]

lemma liminf_le_liminf_add_of_eventually_le {f g : ℕ → ℝ} {c : ℝ}
    (hf : IsBoundedUnder (· ≥ ·) atTop f)
    (hg : IsBoundedUnder (· ≤ ·) atTop g ∧ IsBoundedUnder (· ≥ ·) atTop g)
    (hle : ∀ᶠ n in atTop, f n ≤ g n+c) :
    liminf f atTop ≤ liminf g atTop+c := by
  rw [← liminf_add_const atTop g c hg.1.isCobounded_ge hg.2]
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => g n+c) := by
    obtain ⟨b,hb⟩ := hg.1.eventually_le
    exact isBoundedUnder_of_eventually_le (a := b+c) (hb.mono (fun n hn => by linarith))
  exact liminf_le_liminf hle hf hb.isCobounded_ge
end DilutedSpinGlass

end

end OAI
