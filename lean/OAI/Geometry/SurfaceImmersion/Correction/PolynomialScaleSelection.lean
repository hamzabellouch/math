import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderThreshold
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! Choose a single power of the geometric parameter for the finitely many
smallness conditions in the initial correction block. The exponent is
chosen before the multiplicative constants. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.ExactCorrection

lemma polynomial_scale_smallness {p q μ C d : ℝ}
    (hq : 0 < q) (hμ : 2*p < μ*q) (hC : 0 ≤ C) (hd : 0 < d) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z t : ℝ, 0 < z → z < η →
      0 < t → t ≤ z^μ → C*z^(-p)*t^q < d*z^p := by
  obtain ⟨η,hη,hη1,hsmall⟩ := positive_power_threshold C (μ*q-2*p) d
    (by linarith) hd
  refine ⟨η,hη,hη1,?_⟩
  intro z t hz hzη ht htz
  have hpow : t^q ≤ (z^μ)^q := Real.rpow_le_rpow ht.le htz hq.le
  have he : z^(-p)*(z^μ)^q = z^(μ*q-2*p)*z^p := by
    rw [← Real.rpow_mul hz.le,← Real.rpow_add hz,← Real.rpow_add hz]
    congr 1
    ring
  calc
    C*z^(-p)*t^q ≤ C*z^(-p)*(z^μ)^q :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hC (Real.rpow_nonneg hz.le _))
    _ = (C*z^(μ*q-2*p))*z^p := by rw [mul_assoc,he]; ring
    _ < d*z^p := mul_lt_mul_of_pos_right (hsmall z hz hzη) (Real.rpow_pos_of_pos hz _)

/-- The first correction block uses finitely many strict positive powers
of its scale. Polynomial geometric losses determine an exponent; the
numerical bounds determine only the final parameter threshold. -/
theorem finite_polynomial_scale_selection {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    ∃ μ : ℝ, 1 < μ ∧ ∀ C d : ι → ℝ, (∀ i, 0 ≤ C i) → (∀ i, 0 < d i) →
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z t : ℝ, 0 < z → z < η →
        0 < t → t ≤ z^μ → ∀ i, C i*z^(-p i)*t^(q i) < d i*z^(p i) := by
  classical
  let μ := 2+∑ i, max (2*p i/q i) 0
  have hsum : 0 ≤ ∑ i, max (2*p i/q i) 0 :=
    Finset.sum_nonneg (fun i _ => le_max_right _ _)
  have hμ : 1 < μ := by change 1 < 2+∑ i, max (2*p i/q i) 0; linarith
  have hμq (i : ι) : 2*p i < μ*q i := by
    have hs := Finset.single_le_sum (fun j _ => le_max_right (2*p j/q j) 0) (Finset.mem_univ i)
    have hi : 2*p i/q i < μ := by
      change 2*p i/q i < 2+∑ i, max (2*p i/q i) 0
      linarith [le_max_left (2*p i/q i) 0]
    exact (div_lt_iff₀ (hq i)).mp hi
  refine ⟨μ,hμ,?_⟩
  intro C d hC hd
  choose η hη hη1 hsmall using fun i => polynomial_scale_smallness (hq i) (hμq i) (hC i) (hd i)
  obtain ⟨η₀,hη₀,hη₀1,hall⟩ := finite_positive_threshold η hη
  refine ⟨η₀,hη₀,hη₀1,?_⟩
  intro z t hz hzη ht htz i
  exact hsmall i z t hz (hzη.trans_le (hall i)) ht htz

end ClosedSurfaceR4.ExactCorrection

end

end OAI
