import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonWordIncrement

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma exists_large_tail_cut {K ζ : ℝ} (hK : 0 < K) (hζ : 0 < ζ) :
    ∃ A : ℝ, 0 < A ∧ K*(2048/(A/40)^2) < ζ/8 := by
  let A := 40*(Real.sqrt (16384*K/ζ)+1)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  have hs := Real.sq_sqrt (show 0 ≤ 16384*K/ζ by positivity)
  have hs0 := Real.sqrt_nonneg (16384*K/ζ)
  have hss : 16384*K < ζ*(A/40)^2 := by
    have he : A/40=Real.sqrt (16384*K/ζ)+1 := by dsimp [A]; ring
    rw [he]
    have hd : ζ*(16384*K/ζ)=16384*K := by field_simp
    nlinarith
  have hAp : 0 < (A/40)^2 := by positivity
  rw [←mul_div_assoc,div_lt_iff₀ hAp]
  nlinarith

lemma profile_scale_ratio {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Ω → ℝ) (hS : Measurable S) (hzero : 0 < μ {x | S x ≠ 0})
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) {b F : ℝ} (hb : 0 < b) (hF : 0 < F)
    (hlim : Tendsto (fun n => truncatedVariance μ S (b*r n)/truncatedVariance μ S (r n)) atTop (𝓝 F)) :
    Tendsto (fun n => fluctuationScale μ S (b*r n)/fluctuationScale μ S (r n)) atTop (𝓝 (b^2/F)) := by
  convert tendsto_const_nhds.div hlim hF.ne' using 1
  funext n
  have hv := ne_of_gt (truncatedVariance_pos μ S hS hzero (hr n))
  have hvb := ne_of_gt (truncatedVariance_pos μ S hS hzero (mul_pos hb (hr n)))
  dsimp [fluctuationScale]
  field_simp [(hr n).ne',hv,hvb]
end DirectionalTransience

end

end

end OAI
