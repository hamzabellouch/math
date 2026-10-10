import OAI.Analysis.LipschitzHilbert.Estimates.GlobalTopBoxes
import OAI.Analysis.LipschitzHilbert.Estimates.WeightedMomentIndex

namespace OAI

/-! Globalize the proved local neighborhood estimates by increasing the
natural moment order on distant boxes. The total exceptional area stays
exponentially small and the top's polynomial decay is retained. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem global_top_neighborhood_of_local {α E : Type*} [NormedAddCommGroup E]
    (F : α → ℝ → ℝ → E) (a b r R B : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hB : 0 ≤ B) (M : ℝ≥0∞) (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hlocal : ∀ (p : ℤ × ℤ) (m : ℕ), 1 ≤ m →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^m*M ∧
        ∀ i x z v, x ∈ Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)) →
          |z-(b+R*p.2)| ≤ R → |v| ≤ R → (x,z) ∉ bad →
          (polynomialWeight a r q x*polynomialWeight b R q (z+v))*‖F i x (z+v)‖ ≤
            B*(m:ℝ)) :
    ∃ exceptional : Set (ℝ × ℝ), MeasurableSet exceptional ∧
      (volume.prod volume) exceptional ≤
        (1/4:ℝ≥0∞)^n*M*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x z v, |v| ≤ R → (x,z) ∉ exceptional →
        ‖F i x (z+v)‖ ≤ 256^q*(3*B*(n:ℝ))*
          boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  classical
  choose bad hbad using fun p : ℤ × ℤ => hlocal p
    (weightedMomentIndex n (boxVariationWeight p)) (weightedMomentIndex_pos n hn _)
  have harea (p : ℤ × ℤ) : (volume.prod volume) (bad p) ≤
      ((1/4:ℝ≥0∞)^n*M)*ENNReal.ofReal (boxVariationWeight p) := by
    calc
      _ ≤ (1/4:ℝ≥0∞)^(weightedMomentIndex n (boxVariationWeight p))*M := (hbad p).2.1
      _ ≤ ((1/4:ℝ≥0∞)^n*ENNReal.ofReal (boxVariationWeight p))*M :=
        mul_le_mul' (weightedMomentIndex_tail n _ (boxVariationWeight_pos p)) le_rfl
      _ = _ := by ring
  refine ⟨⋃ p, bad p, MeasurableSet.iUnion (fun p => (hbad p).1),
    global_exceptional_area (volume.prod volume) bad _ harea, ?_⟩
  intro i x z v hv hout
  let p := packetBoxIndex a b r R x z
  have hpout : (x,z) ∉ bad p := fun h => hout (mem_iUnion.mpr ⟨p,h⟩)
  have hx := floor_box_mem_Ico a r x hr
  have hz := packetBoxIndex_vertical a b r R x z hR
  have hbound := (hbad p).2.2 i x z v hx hz hv hpout
  apply topWeight_bound_to_box_decay a b r R x z v (3*B*(n:ℝ)) _ p q hq
    (norm_nonneg _) hr hR (packetBoxIndex_horizontal a b r R x z hr) hz hv
  apply hbound.trans
  have hm := mul_le_mul_of_nonneg_left
    (weightedMomentIndex_le n hn _ (boxVariationWeight_pos p) (boxVariationWeight_le_one p)) hB
  convert hm using 1
  ring

end LipschitzHilbert

end

end OAI
