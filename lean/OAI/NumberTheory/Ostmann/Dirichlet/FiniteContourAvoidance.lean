import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

namespace OAI

noncomputable section
namespace Ostmann.Dirichlet

theorem finite_avoidance_of_separated {I : Type*} [Fintype I]
    (S : Finset ℝ) (points : I → ℝ) (r : ℝ)
    (hcard : S.card < Fintype.card I)
    (hsep : ∀ i j, i≠j → 2*r  ≤  |points i-points j|) :
    ∃ i, ∀ s∈S, r  ≤  |points i-s| := by
  classical
  by_contra h
  push Not at h
  have hbad (i : I) : ∃ s : S, |points i-(s:ℝ)| < r := by
    obtain ⟨s,hs,hd⟩ := h i
    exact ⟨⟨s,hs⟩,hd⟩
  let f : I → S := fun i => (hbad i).choose
  have hf (i : I) : |points i-(f i:ℝ)| < r := (hbad i).choose_spec
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hij
    have hj : |points j-(f i:ℝ)| < r := by rw [he]; exact hf j
    have ht := abs_sub_le (points i) (f i:ℝ) (points j)
    rw [abs_sub_comm (f i:ℝ) (points j)] at ht
    have hs := hsep i j hij
    have hi := hf i
    linarith
  have hc : Fintype.card I  ≤  S.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  omega

theorem nat_grid_separated (a step : ℝ) (hstep : 0 ≤ step)
    {i j : ℕ} (hij : i≠j) : step  ≤  |(a+step*i)-(a+step*j)| := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hijR : (i:ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    have hm := mul_le_mul_of_nonneg_left hijR hstep
    have ha := le_abs_self ((a+step*j)-(a+step*i))
    rw [abs_sub_comm] at ha
    nlinarith
  · have hjiR : (j:ℝ)+1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    have hm := mul_le_mul_of_nonneg_left hjiR hstep
    have ha := le_abs_self ((a+step*i)-(a+step*j))
    nlinarith

theorem exists_mem_Icc_avoiding_finset (S : Finset ℝ) (a b : ℝ) (hab : a<b) :
    ∃ x∈Set.Icc a b, ∀ s∈S, (b-a)/(4*((S.card:ℝ)+1))  ≤  |x-s| := by
  classical
  let step : ℝ := (b-a)/((S.card:ℝ)+1)
  let points : Fin (S.card+1) → ℝ := fun i => a+step*(i:ℕ)
  let r : ℝ := (b-a)/(4*((S.card:ℝ)+1))
  have hden : 0 < (S.card:ℝ)+1 := by positivity
  have hstep : 0 ≤ step := div_nonneg (sub_nonneg.mpr hab.le) hden.le
  have he : step*((S.card:ℝ)+1)=b-a := div_mul_cancel₀ _ (ne_of_gt hden)
  have hr : 2*r ≤ step := by
    have hre : 4*r=step := by dsimp [r,step]; field_simp
    linarith
  have hsep : ∀ i j : Fin (S.card+1), i≠j → 2*r ≤ |points i-points j| := by
    intro i j hij
    have hv : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
    exact hr.trans (nat_grid_separated a step hstep hv)
  obtain ⟨i,hi⟩ := finite_avoidance_of_separated S points r
    (by simp only [Fintype.card_fin]; omega) hsep
  refine ⟨points i, ?_, hi⟩
  constructor
  · dsimp [points]
    exact le_add_of_nonneg_right (mul_nonneg hstep (Nat.cast_nonneg _))
  · have hiR : (i:ℝ) ≤ (S.card:ℝ)+1 := by
      exact_mod_cast (show (i:ℕ) ≤ S.card+1 from Nat.le_of_lt i.isLt)
    have hm := mul_le_mul_of_nonneg_left hiR hstep
    dsimp [points]
    change a+step*(i:ℕ) ≤ b
    linarith

end Ostmann.Dirichlet
end

end OAI
