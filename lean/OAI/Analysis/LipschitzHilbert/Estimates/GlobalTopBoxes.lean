import OAI.Analysis.LipschitzHilbert.Estimates.TopBoxDecay

namespace OAI

/-! Glue the measurable box exceptions across the full plane, retaining
both the summable area estimate and polynomial decay away from the top. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem floor_box_mem_Ico (a r x : ℝ) (hr : 0 < r) :
    x ∈ Ico (a+r*(⌊(x-a)/r⌋:ℤ)) (a+r*((⌊(x-a)/r⌋:ℤ)+1)) := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le ((x-a)/r)) hr.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x-a)/r)) hr
  rw [div_mul_cancel₀ _ hr.ne'] at hlo hhi
  constructor <;> linarith

theorem global_top_box_gluing {α E : Type*} [NormedAddCommGroup E]
    (F : α → ℝ → ℝ → E) (bad : ℤ × ℤ → Set (ℝ × ℝ))
    (hmeas : ∀ p, MeasurableSet (bad p))
    (a b r R A : ℝ) (hr : 0 < r) (hR : 0 < R) (hA : 0 < A)
    (M : ℝ≥0∞) (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (harea : ∀ p, (ENNReal.ofReal (4*A/boxVariationWeight p))^(2*n)*
      (volume.prod volume) (bad p) ≤ (ENNReal.ofReal (2*A))^(2*n)*M)
    (hpoint : ∀ p i x z v,
      x ∈ Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)) → |z-(b+R*p.2)| ≤ R → |v| ≤ R →
      (x,z) ∉ bad p →
      (polynomialWeight a r q x * polynomialWeight b R q (z+v))*‖F i x (z+v)‖ ≤
        4*A/boxVariationWeight p) :
    ∃ exceptional : Set (ℝ × ℝ), MeasurableSet exceptional ∧
      (volume.prod volume) exceptional ≤ (1/4:ℝ≥0∞)^n*M*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x z v, |v| ≤ R → (x,z) ∉ exceptional →
        ‖F i x (z+v)‖ ≤ 256^q*(4*A)*
          boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  refine ⟨⋃ p, bad p, MeasurableSet.iUnion hmeas,
    global_weighted_even_moment_area (volume.prod volume) bad M A hA n hn harea, ?_⟩
  intro i x z v hv hout
  let p := packetBoxIndex a b r R x z
  have hpout : (x,z) ∉ bad p := fun h => hout (mem_iUnion.mpr ⟨p,h⟩)
  have hx : x ∈ Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)) := floor_box_mem_Ico a r x hr
  have hz := packetBoxIndex_vertical a b r R x z hR
  exact topWeight_bound_to_box_decay a b r R x z v (4*A) ‖F i x (z+v)‖ p q hq
    (norm_nonneg _) hr hR (packetBoxIndex_horizontal a b r R x z hr) hz hv
    (hpoint p i x z v hx hz hv hpout)

end LipschitzHilbert

end

end OAI
