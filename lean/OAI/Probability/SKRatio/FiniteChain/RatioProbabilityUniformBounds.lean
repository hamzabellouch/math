import Mathlib
import OAI.Probability.SKRatio.FiniteChain.DiscreteDistanceNonneg

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio

theorem ratio_probability_zero_of_uniform_bounds
    (law : (n : ℕ) → Measure (Disorder n))
    (G : (n : ℕ) → Set (Disorder n)) (T : (n : ℕ) → Disorder n → ℝ)
    {ε η b : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hbase : (1 + b) / (1 - b) < 1 + η)
    (hG : Tendsto (fun n => law n (G n)ᶜ) atTop (𝓝 0))
    (hscale : ∀ A : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, A ≤ T n g)
    (hlower : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1 - ε < discreteDistance g ⌊(1 - b) * T n g⌋₊)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      discreteDistance g ⌈(1 + b) * T n g⌉₊ ≤ ε) :
    Tendsto (fun n => law n
      {g : Disorder n | 1 + η < (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)})
      atTop (𝓝 0) := by
  have hrem : Tendsto (fun t : ℝ => 1 / ((1 - b) * t)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def, id_eq] using
      tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hb1))
  have htail : ∀ᶠ t : ℝ in atTop,
      0 < t ∧ (1 + b) / (1 - b) + 1 / ((1 - b) * t) ≤ 1 + η := by
    filter_upwards [eventually_gt_atTop 0, hrem.eventually (gt_mem_nhds (sub_pos.mpr hbase))]
      with t ht hr
    exact ⟨ht, by linarith only [hr]⟩
  obtain ⟨A, hA⟩ := eventually_atTop.mp htail
  have hsub : ∀ᶠ n : ℕ in atTop,
      {g : Disorder n | 1 + η < (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)} ⊆
        (G n)ᶜ := by
    filter_upwards [hscale A, hlower, hupper] with n hs hl hu
    intro g hg hgG
    obtain ⟨hT, htail⟩ := hA (T n g) (hs g hgG)
    have hratio := mixing_ratio_bound g hε0 hε1 hb0 hb1 hT (hl g hgG) (hu g hgG)
    exact not_lt_of_ge (hratio.trans htail) hg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
  · exact Eventually.of_forall (fun n => by positivity)
  · exact hsub.mono (fun n hn => measure_mono hn)

end SKRatio

noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter

end
end
end
end
end

end OAI
