import OAI.NumberTheory.Jacobsthal.Primes.ReferenceSourcePrimeSets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceProductErrors

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
open ReferenceProductsBasics ReferenceMertens

theorem normalization_eventually_bounded : ∀ᶠ w : ℝ in atTop,1/2 ≤ normalization w ∧ normalization w ≤ 2 := by
  have h := normalization_tendsto_one.eventually
    (Ioo_mem_nhds (by norm_num : (1/2:ℝ)<1) (by norm_num : (1:ℝ)<2))
  filter_upwards [h] with w hw
  exact ⟨hw.1.le,hw.2.le⟩

theorem reference_product_absolute : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → 1/2 ≤ normalization w ∧ normalization w ≤ 2 ∧
      ∀ b : ℝ,2 ≤ b → ∀ closed : Bool,
        |referenceProduct w b closed-normalization w/b| ≤
          (C/b)*Real.exp (-c*Real.sqrt (b*Real.log w)) := by
  obtain ⟨c,C,wM,hc,hC,hwM,h⟩ := reference_product_strong
  obtain ⟨wN,hwN⟩ := eventually_atTop.mp normalization_eventually_bounded
  refine ⟨c,2*C,max wM wN,hc,by positivity,hwM.trans_le (le_max_left _ _),?_⟩
  intro w hw
  have hwm : wM ≤ w := (le_max_left _ _).trans hw
  have hwn := hwN w ((le_max_right _ _).trans hw)
  refine ⟨hwn.1,hwn.2,?_⟩
  intro b hb closed
  have hw1 : 1 < w := hwM.trans_le hwm
  have hb0 : 0 < b := by linarith
  have hD : 0 < normalization w/b := div_pos (normalization_pos hw1) hb0
  have hh := h w hwm b hb closed
  rw [div_sub_one (ne_of_gt hD),abs_div,abs_of_pos hD] at hh
  have hm := (div_le_iff₀ hD).mp hh
  calc
    _ ≤ (C*Real.exp (-c*Real.sqrt (b*Real.log w)))*(normalization w/b) := hm
    _ ≤ (C*Real.exp (-c*Real.sqrt (b*Real.log w)))*(2/b) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hwn.2 hb0.le) (by positivity)
    _ = _ := by ring

end NumberTheoryLean.ReferenceProductErrors

end

end Erdos970

end OAI
