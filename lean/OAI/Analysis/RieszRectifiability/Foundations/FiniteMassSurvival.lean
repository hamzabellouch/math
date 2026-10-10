import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellRegionMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem retained_mass_ge_of_double_fraction {m a : ℝ≥0∞} (hm : m ≠ ⊤) (ha : a ≤ m)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (h : ENNReal.ofReal (2 * θ) * m ≤ a + ENNReal.ofReal θ * m) :
    ENNReal.ofReal θ * m ≤ a := by
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hm ha
  have hright : a + ENNReal.ofReal θ * m ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hright h
  rw [ENNReal.toReal_add hat (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * θ), ENNReal.toReal_ofReal hθ] at hr
  apply (ENNReal.toReal_le_toReal (by finiteness) hat).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ]
  nlinarith

theorem cellRegion_stopping_mass_contraction {d : ℕ}
    (ν : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets ν R hR k).points)
    (Good : SupportCellDescendant ν R hR k z → Prop)
    (hfinite : ν (cleanSupportCell ν R hR k z) ≠ ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hretain : ENNReal.ofReal θ * ν (cleanSupportCell ν R hR k z) ≤
      ν (cellRegionLimit ν R hR k z Good)) :
    (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≤
      ENNReal.ofReal (1 - θ) * ν (cleanSupportCell ν R hR k z) := by
  have hpart := cellRegion_mass_identity ν R hR k z Good
  have hstop := cellRegion_stopping_mass_le_top ν R hR k z Good
  have harea : ν (cellRegionLimit ν R hR k z Good) ≤ ν (cleanSupportCell ν R hR k z) :=
    measure_mono (fun _ hx => hx.1)
  have ha : ν (cellRegionLimit ν R hR k z Good) ≠ ⊤ := ne_top_of_le_ne_top hfinite harea
  have hs : (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite hstop
  have hreal := congrArg ENNReal.toReal hpart
  rw [ENNReal.toReal_add ha hs] at hreal
  have hret := ENNReal.toReal_mono ha hretain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ] at hret
  apply (ENNReal.toReal_le_toReal hs (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hθ1)]
  nlinarith

end

end RieszRectifiability

end OAI
