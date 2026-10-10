import Mathlib
import OAI.Geometry.DoublingHilbert.IntrinsicCovers

namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

theorem intrinsic_doubling_of_distortion36
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {S : Set X} {L : ℕ}
    (hS : AmbientDoubling S L) (p : Y → X) (hp : ∀ y, p y ∈ S)
    {a : ℝ} (ha : 0 < a)
    (hd : ∀ y z, a * dist (p y) (p z) ≤ dist y z ∧
      dist y z ≤ 36 * a * dist (p y) (p z)) :
    ∀ x : Y, ∀ r : ℝ, 0 < r →
      ∃ centers : Finset Y, centers.card ≤ L ^ 8 ∧
        ∀ y : Y, dist y x < r → ∃ c ∈ centers, dist y c < r / 2 := by
  classical
  intro x r hr
  obtain ⟨c, _, hcard, hcov⟩ := ambient_iterated_cover hS 8 (hp x) (div_pos hr ha)
  let meets (z : c) : Prop := ∃ y : Y, dist y x < r ∧
    dist (p y) z.val < r / a / (2 : ℝ) ^ 8
  let chooseCenter (z : c) : Y := if hz : meets z then hz.choose else x
  let cs := c.attach.image chooseCenter
  refine ⟨cs, Finset.card_image_le.trans (by simpa using hcard), ?_⟩
  intro y hy
  have hy' : dist (p y) (p x) < r / a := (lt_div_iff₀ ha).mpr (by
    have h := (hd y x).1
    nlinarith)
  obtain ⟨z, hz, hyz⟩ := hcov (p y) (hp y) hy'
  have hm : meets ⟨z, hz⟩ := ⟨y, hy, hyz⟩
  have hc : dist (p (chooseCenter ⟨z, hz⟩)) z < r / a / (2 : ℝ) ^ 8 := by
    simp only [chooseCenter, dite_eq_left hm]
    exact hm.choose_spec.2
  refine ⟨chooseCenter ⟨z, hz⟩,
    Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  have htri := dist_triangle (p y) z (p (chooseCenter ⟨z, hz⟩))
  rw [dist_comm z] at htri
  have hbound : a * dist (p y) (p (chooseCenter ⟨z, hz⟩)) < r / 128 := by
    calc
      _ ≤ a * (dist (p y) z + dist (p (chooseCenter ⟨z, hz⟩)) z) :=
        mul_le_mul_of_nonneg_left htri ha.le
      _ < a * (r / a / (2 : ℝ) ^ 8 + r / a / (2 : ℝ) ^ 8) :=
        mul_lt_mul_of_pos_left (add_lt_add hyz hc) ha
      _ = r / 128 := by field_simp; ring
  have hu := (hd y (chooseCenter ⟨z, hz⟩)).2
  linarith

theorem range_doubling_of_distortion36
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] {S : Set X} {L : ℕ}
    (hS : AmbientDoubling S L) (p : Z → X) (hp : ∀ z, p z ∈ S)
    (f : Z → Y) {a : ℝ} (ha : 0 < a)
    (hd : ∀ z w, a * dist (p z) (p w) ≤ dist (f z) (f w) ∧
      dist (f z) (f w) ≤ 36 * a * dist (p z) (p w)) :
    DoublingAtMost (Set.range f) (L ^ 8) := by
  classical
  let q : Set.range f → Z := fun y => y.property.choose
  have hq (y : Set.range f) : f (q y) = y.val := y.property.choose_spec
  apply intrinsic_doubling_of_distortion36 hS (p ∘ q) (fun y => hp (q y)) ha
  intro y z
  simpa only [Function.comp_apply, hq, Subtype.dist_eq] using hd (q y) (q z)

end CompactBanach
end

end OAI
