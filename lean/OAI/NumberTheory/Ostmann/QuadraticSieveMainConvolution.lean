import OAI.NumberTheory.Ostmann.QuadraticSieve
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainder

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem sum_oddSquarefree_multiple (e K L : ℕ) (he : 0 < e) (heo : Odd e)
    (hL : e * K ≤ L) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeUpTo K, if P b then f (e * b) else 0) =
      ∑ w ∈ Finset.Icc 1 L,
        if Odd w ∧ e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K ∧ P (w / e) then f w else 0 := by
  classical
  have hsets : (oddSquarefreeUpTo K).image (fun b => e * b) =
      (Finset.Icc 1 L).filter (fun w => Odd w ∧ e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K) := by
    ext w
    constructor
    · intro hw
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
      have h := mem_oddSquarefreeUpTo.mp hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Nat.mul_pos he h.1
      · exact (Nat.mul_le_mul_left e h.2.1).trans hL
      · simpa only [Nat.mul_div_cancel_left b he] using
          (show Odd (e * b) ∧ e ∣ e * b ∧ Squarefree b ∧ b ≤ K from
            ⟨heo.mul h.2.2.1, dvd_mul_right _ _, h.2.2.2, h.2.1⟩)
    · intro hw
      have h := (Finset.mem_filter.mp hw).2
      have hb : w / e ∈ oddSquarefreeUpTo K := mem_oddSquarefreeUpTo.mpr
        ⟨Nat.pos_of_ne_zero h.2.2.1.ne_zero, h.2.2.2,
          h.1.of_dvd_nat (Nat.div_dvd_of_dvd h.2.1), h.2.2.1⟩
      exact Finset.mem_image.mpr ⟨w / e, hb, Nat.mul_div_cancel' h.2.1⟩
  let F : ℕ → ℂ := fun w => if P (w / e) then f w else 0
  calc
    _ = ∑ b ∈ oddSquarefreeUpTo K, F (e * b) := by
      apply Finset.sum_congr rfl
      intro b hb
      simp only [F, Nat.mul_div_cancel_left b he]
    _ = ∑ w ∈ (oddSquarefreeUpTo K).image (fun b => e * b), F w := by
      symm
      exact Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left he h)
    _ = _ := by
      rw [hsets, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [F]
      by_cases h : Odd w ∧ e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K
      · by_cases hp : P (w / e) <;> simp [h, hp]
      · have hn : ¬(Odd w ∧ e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K ∧ P (w / e)) := by
          tauto
        simp [h, hn]

end Ostmann.QuadraticSieve

end OAI
