import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationStars
import OAI.Combinatorics.KMedian.Preparation.PreparationInner

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T Ω Ξ : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype Ω] [Fintype Ξ]

omit [DecidableEq T] in

theorem preparation_old_cost (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
    (P : T → Finset I) (y d : I → ℝ) (p : T → ℝ) (p' : Ω → T → ℝ)
    (U : Ω → I → ℝ) (Y : Ω → Ξ → T × I → ℝ) (F : Finset I) {p₀ : ℝ}
    (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hp : ∀ t, p₀ ≤ p t) (hcap : ∀ ω t, p' ω t ≤ 1)
    (hUm : ∀ i, ν.expect (fun ω => U ω i)=y i)
    (hYm : ∀ ω t i, (κ ω).expect (fun ξ => Y ω ξ (t,i))=
      if i ∈ P t then p' ω t*y i/p t else 0) :
    (ν.joint κ).expect (fun z =>
      (∑ i ∈ F ∩ SupplierStars.outside P, U z.1 i*d i)+
      (∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i)*d i)) ≤ (∑ i ∈ F, y i*d i)/p₀ := by
  let a := fun t => ∑ i ∈ F ∩ P t, y i*d i
  let u := ∑ i ∈ F ∩ SupplierStars.outside P, y i*d i
  have ha : ∀ t, 0 ≤ a t := fun t => sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
  have hu : 0 ≤ u := sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
  have hpart : u+(∑ t, a t)=∑ i ∈ F, y i*d i := SupplierStars.mass_partition (fun i => y i*d i) P hP F
  have hinner : ∀ ω, (κ ω).expect (fun ξ => ∑ t, ∑ i ∈ F, Y ω ξ (t,i)*d i)=
      ∑ t, (p' ω t/p t)*a t := by
    intro ω
    rw [FiniteLaw.expect_sum]
    exact sum_congr rfl (fun t _ => rescaled_subset_mean (κ ω) (Y ω) P y p (p' ω) (hYm ω) F d t)
  have hbound : ∀ ω, (∑ t, (p' ω t/p t)*a t) ≤ (∑ t, a t)/p₀ := by
    intro ω
    rw [sum_div]
    apply sum_le_sum
    intro t _
    have hpp : 0 < p t := hp₀.trans_le (hp t)
    calc
      (p' ω t/p t)*a t ≤ (1/p t)*a t := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hcap ω t) hpp.le) (ha t)
      _ ≤ (1/p₀)*a t := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hp₀ (hp t)) (ha t)
      _ = a t/p₀ := by ring
  have hout : ν.expect (fun ω => ∑ i ∈ F ∩ SupplierStars.outside P, U ω i*d i)=u := by
    rw [FiniteLaw.expect_sum]
    simp only [FiniteLaw.expect_mul_right,hUm,u]
  rw [FiniteLaw.expect_joint]
  simp only [FiniteLaw.expect_add,FiniteLaw.expect_const,hinner]
  rw [hout]
  have he := (ν.expect_mono hbound).trans_eq (ν.expect_const _)
  have hue : u ≤ u/p₀ := (le_div_iff₀ hp₀).mpr (mul_le_of_le_one_right hu hp₀1)
  calc
    _ ≤ u/p₀+(∑ t, a t)/p₀ := add_le_add hue he
    _ = (u+∑ t, a t)/p₀ := (add_div _ _ _).symm
    _ = _ := by rw [hpart]

end MetricKMedian.Preparation
end
end

end OAI
