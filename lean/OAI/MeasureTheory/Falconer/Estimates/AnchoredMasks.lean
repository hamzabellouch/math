import OAI.MeasureTheory.Falconer.Measures.MaskProductBudget
import OAI.MeasureTheory.Falconer.Estimates.DyadicTree

namespace OAI

/-!
# Angular masks attached to actual dyadic anchor cells

The spatial dependence is a finite Borel choice of the anchor cell.
On every descendant of an anchor cell, its angular mask is exactly
constant in the spatial variable.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def anchoredMask {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ) (x : Space d) (w : Sphere d) : ℝ :=
  ∑ p ∈ cubePaths d n, if x ∈ (Q.descendant p).carrier then F p w else 0

theorem anchoredMask_measurable {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ) (hF : ∀ p, Measurable (F p)) :
    Measurable (Function.uncurry (anchoredMask Q n F)) := by
  apply Finset.measurable_sum
  intro p _
  exact ((hF p).comp measurable_snd).ite
    ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

theorem anchoredMask_on_cell {d n : ℕ} (Q : DyadicCube d)
    (F : List (Fin d → Bool) → Sphere d → ℝ) (p : List (Fin d → Bool)) (hp : p.length = n)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d) :
    anchoredMask Q n F x w = F p w := by
  unfold anchoredMask
  rw [Finset.sum_eq_single p]
  · simp [hx]
  · intro q hq hqp
    have hdis := Q.descendants_disjoint ((mem_cubePaths d n q).mp hq |>.trans hp.symm) hqp
    have hn : x ∉ (Q.descendant q).carrier := fun hq => Set.disjoint_left.mp hdis hq hx
    simp [hn]
  · exact fun hn => (hn ((mem_cubePaths d n p).mpr hp)).elim

theorem anchoredMask_off_parent {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ) {x : Space d} (hx : x ∉ Q.carrier)
    (w : Sphere d) : anchoredMask Q n F x w = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  have hn : x ∉ (Q.descendant p).carrier := fun h => hx (Q.descendant_subset p h)
  simp [hn]

theorem anchoredMask_bounds {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ)
    (hF : ∀ p ∈ cubePaths d n, ∀ w, 0 ≤ F p w ∧ F p w ≤ 1)
    (x : Space d) (w : Sphere d) :
    0 ≤ anchoredMask Q n F x w ∧ anchoredMask Q n F x w ≤ 1 := by
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth n hx
    rw [anchoredMask_on_cell Q F p ((mem_cubePaths d n p).mp hp) hxp]
    exact hF p hp w
  · rw [anchoredMask_off_parent Q n F hx]
    norm_num

theorem anchoredMask_reached {d n : ℕ} (Q : DyadicCube d)
    (F : List (Fin d → Bool) → Sphere d → ℝ)
    (p q : List (Fin d → Bool)) (hp : p.length = n)
    {x : Space d} (hx : x ∈ (Q.descendant (p++q)).carrier) (w : Sphere d) :
    anchoredMask Q n F x w = F p w := by
  rw [Q.descendant_append] at hx
  exact anchoredMask_on_cell Q F p hp ((Q.descendant p).descendant_subset q hx) w

theorem anchoredMask_chart_smooth {n g : ℕ} (Q : DyadicCube (n+2))
    (F : List (Fin (n+2) → Bool) → Sphere (n+2) → ℝ)
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n)
    (hF : ∀ p ∈ cubePaths (n+2) g,
      ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (F p w : ℂ)) y))
    (x : Space (n+2)) :
    ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (anchoredMask Q g F x w : ℂ)) y) := by
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth g hx
    have he : anchoredMask Q g F x = F p := by
      funext w
      exact anchoredMask_on_cell Q F p ((mem_cubePaths (n+2) g p).mp hp) hxp w
    rw [he]
    exact hF p hp
  · have he : anchoredMask Q g F x = fun _ => 0 := by
      funext w
      exact anchoredMask_off_parent Q g F hx w
    rw [he]
    exact contDiff_const


theorem anchoredMask_chart_derivatives {n g : ℕ} (Q : DyadicCube (n+2))
    (F : List (Fin (n+2) → Bool) → Sphere (n+2) → ℝ)
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n)
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (m : ℕ)
    (hF : ∀ p ∈ cubePaths (n+2) g, ∀ u ∈ Icc (-1 : ℝ) 1, ∀ k ≤ m,
      ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (F p w : ℂ)) y) u‖ ≤ B*D^k)
    (x : Space (n+2)) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (k : ℕ) (hk : k ≤ m) :
    ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (anchoredMask Q g F x w : ℂ)) y) u‖ ≤ B*D^k := by
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth g hx
    have he : anchoredMask Q g F x = F p := by
      funext w
      exact anchoredMask_on_cell Q F p ((mem_cubePaths (n+2) g p).mp hp) hxp w
    rw [he]
    exact hF p hp u hu k hk
  · have he : anchoredMask Q g F x = fun _ => 0 := by
      funext w
      exact anchoredMask_off_parent Q g F hx w
    rw [he]
    change ‖iteratedDeriv k (fun _ : ℝ => (0 : ℂ)) u‖ ≤ _
    simp only [iteratedDeriv_const,ite_self,norm_zero]
    exact mul_nonneg hB (pow_nonneg hD k)

end Falconer

end OAI
