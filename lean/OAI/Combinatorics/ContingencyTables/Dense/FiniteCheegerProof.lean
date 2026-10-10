import OAI.Combinatorics.ContingencyTables.Dense.CheegerPositive
import OAI.Combinatorics.ContingencyTables.Dense.CheegerMedian

namespace OAI

/-! # Discharging the finite-chain Cheeger input by coarea and a weighted median -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

private lemma split_square (u : ℝ) : (max u 0)^2+(max (-u) 0)^2 = u^2 := by
  by_cases hu : 0 ≤ u
  · rw [max_eq_left hu,max_eq_right (neg_nonpos.mpr hu)]
    ring
  · rw [max_eq_right (le_of_not_ge hu),max_eq_left (by linarith)]
    ring

private lemma split_difference (u v : ℝ) :
    (max u 0-max v 0)^2+(max (-u) 0-max (-v) 0)^2 ≤ (u-v)^2 := by
  by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v
  · rw [max_eq_left hu,max_eq_left hv,max_eq_right (neg_nonpos.mpr hu),
      max_eq_right (neg_nonpos.mpr hv)]
    simp
  · have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_left hu,max_eq_right hv',max_eq_right (neg_nonpos.mpr hu),
      max_eq_left (neg_nonneg.mpr hv')]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hu hv']
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [max_eq_right hu',max_eq_left hv,max_eq_left (neg_nonneg.mpr hu'),
      max_eq_right (neg_nonpos.mpr hv)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hu' hv]
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hv' : v ≤ 0 := le_of_not_ge hv
    rw [max_eq_right hu',max_eq_right hv',max_eq_left (neg_nonneg.mpr hu'),
      max_eq_left (neg_nonneg.mpr hv')]
    nlinarith

variable {X : Type*} [Fintype X]

/-- Levin–Peres Theorem 13.10 lower bound, in the exact finite Poincaré form used here. -/
theorem finiteCheeger : PublishedInputs.FiniteCheeger X := by
  intro C κ hk hcut f
  obtain ⟨a,hbelow,habove⟩ := exists_median C f
  let p : X → ℝ := fun x => max (f x-a) 0
  let n : X → ℝ := fun x => max (a-f x) 0
  have hp : mass C (Finset.univ.filter fun x => 0 < p x) ≤ 1/2 := by
    simpa only [p,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using habove
  have hn : mass C (Finset.univ.filter fun x => 0 < n x) ≤ 1/2 := by
    simpa only [n,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using hbelow
  have hcut' : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S := hcut
  have hpe := positive_energy C κ hk hcut' p (fun _ => le_max_right _ _) hp
  have hne := positive_energy C κ hk hcut' n (fun _ => le_max_right _ _) hn
  have hnorm : (∑ x, C.π x*(p x)^2)+(∑ x, C.π x*(n x)^2) =
      ∑ x, C.π x*(f x-a)^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [p,n]
    rw [← mul_add,show a-f x = -(f x-a) by ring,split_square]
  have he : C.energy p+C.energy n ≤ C.energy f := by
    rw [C.energy_eq,C.energy_eq,C.energy_eq,← add_div,
      ← Finset.sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (C.positive x).le (C.nonnegative x y))
    dsimp [p,n]
    convert split_difference (f x-a) (f y-a) using 1 <;> ring_nf
  have hv := mul_le_mul_of_nonneg_left (variance_le_centered C f a) (sq_nonneg κ)
  have hb : κ^2*C.variance f ≤ 2*C.energy f := by
    rw [← hnorm] at hv
    nlinarith [hpe,hne,he]
  have hk2 : 0 < κ^2 := sq_pos_of_pos hk
  calc
    C.variance f ≤ (2*C.energy f)/κ^2 := (le_div_iff₀ hk2).mpr (by nlinarith [hb])
    _ = (2/κ^2)*C.energy f := by ring

end
end ContingencyTables.CheegerProof

end OAI
