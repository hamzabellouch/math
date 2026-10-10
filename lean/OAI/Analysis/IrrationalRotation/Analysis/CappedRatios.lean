import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Topology.Order.Lattice

namespace OAI

namespace Invariant233

variable {X : Type*}

theorem norm_capped_ratio_le {B a b : ℝ}
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(Complex.ofReal (min B (a / b)))‖ ≤ B := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_min hB (div_nonneg ha hb))]
  exact min_le_left _ _

theorem capped_ratio_eq_of_le {B a b : ℝ} (h : a / b ≤ B) :
    (Complex.ofReal (min B (a / b))) = (a / b : ℝ) := by
  rw [min_eq_right h]

theorem measurable_capped_ratio [MeasurableSpace X]
    (F : X → ℝ) (hF : Measurable F) (B : ℝ) :
    Measurable (fun t : X × X => (Complex.ofReal (min B (F t.2 / F t.1)))) :=
  Complex.measurable_ofReal.comp
    (measurable_const.min ((hF.comp measurable_snd).div (hF.comp measurable_fst)))

theorem continuousOn_capped_ratio [TopologicalSpace X]
    (F : X → ℝ) (Q : Set X) (hF : ContinuousOn F Q)
    (hFp : ∀ x ∈ Q, F x ≠ 0) (B : ℝ) :
    ContinuousOn (fun t : X × X => (Complex.ofReal (min B (F t.2 / F t.1)))) (Q ×ˢ Q) := by
  have hfst : ContinuousOn (fun t : X × X => F t.1) (Q ×ˢ Q) :=
    hF.comp continuous_fst.continuousOn (fun _ ht => ht.1)
  have hsnd : ContinuousOn (fun t : X × X => F t.2) (Q ×ˢ Q) :=
    hF.comp continuous_snd.continuousOn (fun _ ht => ht.2)
  have hratio : ContinuousOn (fun t : X × X => F t.2 / F t.1) (Q ×ˢ Q) :=
    hsnd.div hfst (fun t ht => hFp t.1 ht.1)
  exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.inf hratio)

end Invariant233

end OAI
