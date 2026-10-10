import OAI.MeasureTheory.Falconer.Estimates.Packing
import Mathlib.Order.SuccPred.Archimedean

namespace OAI

/-! # Finite nets in a Euclidean ball with the dimension-sharp cardinal bound -/

namespace Falconer
open Set Metric

theorem finite_euclidean_ball_net (d : ℕ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ S : Finset (Space d), (∀ x ∈ S, ‖x‖ ≤ R) ∧
      (∀ x : Space d, ‖x‖ ≤ R → ∃ y ∈ S, dist x y ≤ δ) ∧
      (S.card : ℝ) ≤ (2*R/δ+1)^d := by
  classical
  let P : Finset (Space d) → Prop := fun S => (∀ x ∈ S, ‖x‖ ≤ R) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < dist x y)
  have hcard (S : Finset (Space d)) (hS : P S) : (S.card:ℝ) ≤ (2*R/δ+1)^d :=
    separated_ball_card S 0 hδ hR (fun x hx y hy hxy => (hS.2 x hx y hy hxy).le)
      (fun x hx => by simpa only [dist_zero_right] using hS.1 x hx)
  let K : Set ℕ := {n | ∃ S : Finset (Space d), P S ∧ S.card = n}
  have hbounded : BddAbove K := by
    obtain ⟨N,hN⟩ := exists_nat_ge ((2*R/δ+1)^d)
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨S,hS,rfl⟩ := hn
    exact_mod_cast (hcard S hS).trans hN
  have hnonempty : K.Nonempty := ⟨0,∅,by simp [P],rfl⟩
  obtain ⟨n,hn,hmax⟩ := hbounded.exists_isGreatest_of_nonempty hnonempty
  obtain ⟨S,hS,hSn⟩ := hn
  refine ⟨S,hS.1,?_,hcard S hS⟩
  intro x hx
  by_contra hnocover
  have hfar : ∀ y ∈ S, δ < dist x y := by
    simpa only [not_exists,not_and,not_le] using hnocover
  have hxS : x ∉ S := by
    intro hh
    have hh' := hfar x hh
    simp only [dist_self] at hh'
    exact (not_lt_of_ge hδ.le) hh'
  have hnew : P (insert x S) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hS.1 y hy
    · intro y hy z hz hyz
      by_cases hyx : y = x
      · subst y
        exact hfar z (Finset.mem_of_mem_insert_of_ne hz (Ne.symm hyz))
      · have hyS : y ∈ S := Finset.mem_of_mem_insert_of_ne hy hyx
        by_cases hzx : z = x
        · subst z
          simpa only [dist_comm] using hfar y hyS
        · exact hS.2 y hyS z (Finset.mem_of_mem_insert_of_ne hz hzx) hyz
  have hh := hmax (show (insert x S).card ∈ K from ⟨insert x S,hnew,rfl⟩)
  rw [Finset.card_insert_of_notMem hxS,← hSn] at hh
  omega

end Falconer

end OAI
