import OAI.NumberTheory.Ostmann.QuadraticCenter.IncidenceFactorial

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset

theorem common_center_from_moments
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : ι → Finset α) (n lo t k mass : ℕ)
    (hlo : lo ≤ n + 1) (hpos : 0 < mass)
    (hmoment : mass + t ^ (n + 1 - lo) * ∑ i, (A i).card.descFactorial lo ≤
      ∑ i, (A i).card.descFactorial (n + 1))
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ k)
    (hgap : 2 * k * Fintype.card α ≤ t ^ 2) :
    ∃ i, t ≤ (A i).card ∧
      (mass : ℝ) ≤ 2 * (Fintype.card α : ℝ) * ((A i).card : ℝ) ^ n := by
  classical
  have hhigh := high_rows_moment_lower (fun i => (A i).card) lo (n + 1) t mass
    hlo hmoment
  let H := {i : ι // t ≤ (A i).card}
  have hne : Nonempty H := by
    by_contra h
    have hzero : (∑ i ∈ Finset.univ.filter (fun i => t ≤ (A i).card),
        (A i).card.descFactorial (n + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact False.elim (h ⟨⟨i, (Finset.mem_filter.mp hi).2⟩⟩)
    omega
  have : Nonempty H := hne
  have hmass : (mass : ℝ) ≤ ∑ i : H, ((A i.val).card.descFactorial (n + 1) : ℝ) := by
    have heq : (∑ i : H, (A i.val).card.descFactorial (n + 1)) =
        ∑ i ∈ Finset.univ.filter (fun i => t ≤ (A i).card),
          (A i).card.descFactorial (n + 1) := by
      simpa [H] using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun i => t ≤ (A i).card) (fun i => (A i).card.descFactorial (n + 1)))
    have hnat : mass ≤ ∑ i : H, (A i.val).card.descFactorial (n + 1) := by
      rw [heq]
      exact hhigh
    exact_mod_cast hnat
  obtain ⟨i, hi⟩ := exists_large_row (fun i : H => A i.val) n k t mass
    (by positivity) (by positivity) (fun i => by exact_mod_cast i.property)
    (fun i j hij => by
      exact_mod_cast hinter i.val j.val (fun h => hij (Subtype.ext h)))
    (by exact_mod_cast hgap) hmass
  exact ⟨i.val, i.property, hi⟩

end Ostmann.QuadraticCenter

end OAI
