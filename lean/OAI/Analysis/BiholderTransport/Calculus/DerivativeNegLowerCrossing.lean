import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma derivative_neg_of_lower_crossing {f : ℝ → ℝ} {d a c : ℝ}
    (hd : HasDerivAt f d 1) (ha : a < 1) (hc : 0 < c)
    (hf : ∀ᶠ t in 𝓝 (1:ℝ), a < t → t < 1 → c*(1-t) ≤ f t-f 1) : 0 < -d := by
  have Hsl : Tendsto (slope f 1) (𝓝[<] (1:ℝ)) (𝓝 d) :=
    hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1)
  have Hle : ∀ᶠ t in 𝓝[<] (1:ℝ), slope f 1 t ≤ -c := by
    filter_upwards [hf.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hat ht1
    have H := ht hat ht1
    rw [slope_def_field]
    exact (div_le_iff_of_neg (sub_neg.mpr ht1)).mpr (by nlinarith only [H])
  have H := le_of_tendsto Hsl Hle
  linarith only [H,hc]

end WeakMTWTransport

end

end OAI
