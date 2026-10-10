import OAI.Probability.SLE.Loewner.SlitSegmentParameter

namespace OAI

/-! An explicit sequence approaching the terminal parameter from below,
with every point still after the initial parameter. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

noncomputable def approachIntervalEndpoint {s t : unitInterval} (hst : s<t) (n : ℕ) :
    unitInterval := by
  let d : ℝ := (t:ℝ)-(s:ℝ)
  have hd : 0<d := sub_pos.mpr hst
  have hden : 0<(n:ℝ)+1 := by positivity
  have he : d/((n:ℝ)+1)≤d := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨(t:ℝ)-d/((n:ℝ)+1),?_,?_⟩
  · dsimp only [d] at he ⊢
    linarith [s.property.1]
  · have hq := div_pos hd hden
    linarith [t.property.2]

lemma approachIntervalEndpoint_mem {s t : unitInterval} (hst : s<t) (n : ℕ) :
    approachIntervalEndpoint hst n∈Ico s t := by
  have hd : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hden : 0<(n:ℝ)+1 := by positivity
  have he : ((t:ℝ)-(s:ℝ))/((n:ℝ)+1)≤(t:ℝ)-(s:ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  constructor
  · change (s:ℝ)≤(t:ℝ)-((t:ℝ)-(s:ℝ))/((n:ℝ)+1)
    linarith
  · change (t:ℝ)-((t:ℝ)-(s:ℝ))/((n:ℝ)+1)<(t:ℝ)
    linarith [div_pos hd hden]

lemma approachIntervalEndpoint_tendsto {s t : unitInterval} (hst : s<t) :
    Tendsto (approachIntervalEndpoint hst) atTop (𝓝 t) := by
  apply tendsto_subtype_rng.mpr
  have hh := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((t:ℝ)-(s:ℝ))).const_sub (t:ℝ)
  convert! hh using 1
  · funext n
    change (t:ℝ)-((t:ℝ)-(s:ℝ))/((n:ℝ)+1)=_
    rw [mul_one_div]
  · simp only [mul_zero,sub_zero]

end SLEExactGauge

end

end OAI
