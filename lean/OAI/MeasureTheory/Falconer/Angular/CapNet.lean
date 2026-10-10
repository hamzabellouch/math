import OAI.MeasureTheory.Falconer.Estimates.Packing
import Mathlib.Order.SuccPred.Archimedean

namespace OAI

/-!
# A separated finite cap net with uniform local multiplicity

The cardinality maximization takes place in the natural numbers. It needs
only the proved Euclidean packing bound, so no selection of infinitely many
centers or measurable choice is involved.
-/

namespace Falconer
open Set Metric

private theorem sphere_separated_card {d : ℕ} (S : Finset (Sphere d)) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y) :
    (S.card : ℝ) ≤ (4/δ+1)^d := by
  have hinj : Function.Injective (fun x : Sphere d => (x : Space d)) := Subtype.val_injective
  have hh := separated_ball_card (S.image (fun x : Sphere d => (x : Space d))) (0 : Space d)
    (half_pos hδ) (show (0 : ℝ) ≤ 1 by norm_num) (by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact (hsep a ha b hb (fun hab => hxy (congrArg Subtype.val hab))).le) (by
      intro x hx
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      simpa only [dist_zero_right,sphere_norm] using (le_refl (1 : ℝ)))
  rw [Finset.card_image_of_injective S hinj] at hh
  have hr : 2*1/(δ/2)+1 = 4/δ+1 := by ring
  simpa only [hr] using hh

theorem finite_separated_cap_net (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Sphere d),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y) ∧
      (∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) ∧
      (S.card : ℝ) ≤ (4/δ+1)^d ∧
      (∀ w : Sphere d, ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^d) := by
  classical
  let P : Finset (Sphere d) → Prop := fun S =>
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y
  let K : Set ℕ := {k | ∃ S : Finset (Sphere d), P S ∧ S.card = k}
  have hK : BddAbove K := by
    obtain ⟨N,hN⟩ := exists_nat_ge ((4/δ+1)^d)
    refine ⟨N,?_⟩
    intro k hk
    obtain ⟨S,hS,rfl⟩ := hk
    exact_mod_cast (sphere_separated_card S hδ hS).trans hN
  have hne : K.Nonempty := ⟨0,∅,(by simp [P]),rfl⟩
  obtain ⟨k,hk,hmax⟩ := hK.exists_isGreatest_of_nonempty hne
  obtain ⟨S,hS,hcard⟩ := hk
  refine ⟨S,hS,?_,sphere_separated_card S hδ hS,?_⟩
  · intro w
    by_contra hn
    have hfar : ∀ c ∈ S, δ/2 < dist w c := by
      simpa only [not_exists,not_and,not_le] using hn
    have hw : w ∉ S := by
      intro hw
      have hh := hfar w hw
      simp only [dist_self] at hh
      linarith
    have hS' : P (insert w S) := by
      intro x hx y hy hxy
      by_cases hxw : x = w
      · subst x
        have hyw : y ≠ w := fun h => hxy h.symm
        have hyS : y ∈ S := Finset.mem_of_mem_insert_of_ne hy hyw
        exact hfar y hyS
      · have hxS : x ∈ S := Finset.mem_of_mem_insert_of_ne hx hxw
        by_cases hyw : y = w
        · subst y
          simpa only [dist_comm] using hfar x hxS
        · exact hS x hxS y (Finset.mem_of_mem_insert_of_ne hy hyw) hxy
    have hbad := hmax (show (insert w S).card ∈ K from ⟨insert w S,hS',rfl⟩)
    rw [Finset.card_insert_of_notMem hw,← hcard] at hbad
    omega
  · intro w
    exact separated_sphere_overlap S hδ (fun x hx y hy hxy => (hS x hx y hy hxy).le) w

end Falconer

end OAI
