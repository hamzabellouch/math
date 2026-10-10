import OAI.MeasureTheory.Falconer.Slicing.SliceNormalization

namespace OAI

/-! # One common polynomial loss for both normalized slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem polynomial_slice_normalization
    (α : Measure X) (β : Measure Y) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (E : Set (X × Y)) {K V : ℝ} (hK : 0 < K) (hV : 0 < V)
    (hα : α univ ≤ ENNReal.ofReal (K^6)) (hβ : β univ ≤ ENNReal.ofReal (K^3))
    (hI : ENNReal.ofReal (1/(4*K*V)) ≤ (α.prod β) E) :
    ∃ ha : α univ ≠ 0, ∃ hb : β univ ≠ 0,
      ENNReal.ofReal (K^6) / α univ ≤ ENNReal.ofReal (4*K^10*V) ∧
      ENNReal.ofReal (K^3) / β univ ≤ ENNReal.ofReal (4*K^10*V) ∧
      (∀ (S : Set X) (w : ℝ), α S ≤ ENNReal.ofReal (K^6*w) →
        (normalizedSliceLaw α ha : Measure X) S ≤ ENNReal.ofReal (4*K^10*V*w)) ∧
      (∀ (S : Set Y) (w : ℝ), β S ≤ ENNReal.ofReal (K^3*w) →
        (normalizedSliceLaw β hb : Measure Y) S ≤ ENNReal.ofReal (4*K^10*V*w)) ∧
      ENNReal.ofReal (1/(4*K^10*V)) ≤
        ((normalizedSliceLaw α ha : Measure X).prod (normalizedSliceLaw β hb : Measure Y)) E := by
  have hIp : 0 < ENNReal.ofReal (1/(4*K*V)) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨ha,hb⟩ := positive_incidence_marginals α β E (hIp.trans_le hI)
  have hlo := incidence_marginal_lower_bounds α β E hα hβ
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hK 6))) ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hK 3))) ENNReal.ofReal_ne_top hI
  have hla : ENNReal.ofReal (1/(4*K^4*V)) ≤ α univ := by
    convert hlo.1 using 1
    rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 3)]
    congr 1
    field_simp
  have hlb : ENNReal.ofReal (1/(4*K^7*V)) ≤ β univ := by
    convert hlo.2 using 1
    rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 6)]
    congr 1
    field_simp
  have hra : ENNReal.ofReal (K^6) / α univ ≤ ENNReal.ofReal (4*K^10*V) := by
    apply (mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hla)).trans_eq
    change ENNReal.ofReal (K^6) / ENNReal.ofReal (1/(4*K^4*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  have hrb : ENNReal.ofReal (K^3) / β univ ≤ ENNReal.ofReal (4*K^10*V) := by
    apply (mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hlb)).trans_eq
    change ENNReal.ofReal (K^3) / ENNReal.ofReal (1/(4*K^7*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  refine ⟨ha,hb,hra,hrb,?_,?_,?_⟩
  · intro S w hS
    apply (normalizedSliceLaw_bound α ha S hla hS).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (K^6*w) / ENNReal.ofReal (1/(4*K^4*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · intro S w hS
    apply (normalizedSliceLaw_bound β hb S hlb hS).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (K^3*w) / ENNReal.ofReal (1/(4*K^7*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · have hi := normalizedSliceLaw_incidence_lower α β ha hb E hα hβ hI
    convert hi using 1
    symm
    rw [mul_comm,← ENNReal.ofReal_mul (by positivity : 0 ≤ K^6)]
    change ENNReal.ofReal (1/(4*K*V)) / ENNReal.ofReal (K^6*K^3) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp

end Falconer

end OAI
