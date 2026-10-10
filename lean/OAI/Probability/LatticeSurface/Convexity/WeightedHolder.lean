import Mathlib

namespace OAI

open scoped BigOperators

namespace SparseHoles

lemma weighted_holder {ι : Type*} (F : Finset ι) (a W g : ι → ℝ)
    (ha : ∀ e∈F, 0 < a e) (hW : ∀ e∈F, 0 ≤ W e) (hg : ∀ e∈F, 0 ≤ g e)
    (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (∑ e∈F, W e*(g e)^p)^(1/p) ≤
      (∑ e∈F, a e*(g e)^2)^(1/2:ℝ) *
      (∑ e∈F, (W e)^(2/(2-p))*(a e)^(-p/(2-p)))^((2-p)/(2*p)) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < 2-p := by linarith
  have hc : (2/p).HolderConjugate (2/(2-p)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨(lt_div_iff₀ hp0).mpr (by linarith),?_⟩
    field_simp
    ring
  let f : ι → ℝ := fun e => (a e)^(p/2)*(g e)^p
  let h : ι → ℝ := fun e => W e*(a e)^(-p/2)
  have hf : ∀ e∈F, 0 ≤ f e := fun e he =>
    mul_nonneg (Real.rpow_nonneg (ha e he).le _) (Real.rpow_nonneg (hg e he) _)
  have hh : ∀ e∈F, 0 ≤ h e := fun e he =>
    mul_nonneg (hW e he) (Real.rpow_nonneg (ha e he).le _)
  have hprod (e) (he : e∈F) : f e*h e=W e*(g e)^p := by
    dsimp [f,h]
    calc
      _ = W e*(g e)^p*((a e)^(p/2)*(a e)^(-p/2)) := by ring
      _ = _ := by rw [← Real.rpow_add (ha e he)];ring_nf;rw [Real.rpow_zero];ring
  have hfp (e) (he : e∈F) : (f e)^(2/p)=a e*(g e)^2 := by
    dsimp [f]
    rw [Real.mul_rpow (Real.rpow_nonneg (ha e he).le _) (Real.rpow_nonneg (hg e he) _),
      ← Real.rpow_mul (ha e he).le,← Real.rpow_mul (hg e he)]
    have h1 : p/2*(2/p)=1 := by field_simp
    have h2 : p*(2/p)=2 := by field_simp
    rw [h1,h2,Real.rpow_one,Real.rpow_two]
  have hhp (e) (he : e∈F) : (h e)^(2/(2-p))=(W e)^(2/(2-p))*(a e)^(-p/(2-p)) := by
    dsimp [h]
    rw [Real.mul_rpow (hW e he) (Real.rpow_nonneg (ha e he).le _),← Real.rpow_mul (ha e he).le]
    congr 2
    ring
  have hhold := Real.inner_le_Lp_mul_Lq_of_nonneg F hc hf hh
  rw [Finset.sum_congr rfl hprod,Finset.sum_congr rfl hfp,Finset.sum_congr rfl hhp] at hhold
  have hleft : 0 ≤ ∑ e∈F, W e*(g e)^p :=
    Finset.sum_nonneg fun e he => mul_nonneg (hW e he) (Real.rpow_nonneg (hg e he) _)
  have hE : 0 ≤ ∑ e∈F, a e*(g e)^2 :=
    Finset.sum_nonneg fun e he => mul_nonneg (ha e he).le (sq_nonneg _)
  have hS : 0 ≤ ∑ e∈F, (W e)^(2/(2-p))*(a e)^(-p/(2-p)) :=
    Finset.sum_nonneg fun e he => mul_nonneg (Real.rpow_nonneg (hW e he) _) (Real.rpow_nonneg (ha e he).le _)
  refine (Real.rpow_le_rpow hleft hhold (one_div_nonneg.mpr hp0.le)).trans_eq ?_
  rw [Real.mul_rpow (Real.rpow_nonneg hE _) (Real.rpow_nonneg hS _),← Real.rpow_mul hE,← Real.rpow_mul hS]
  congr 2 <;> field_simp

end SparseHoles

end OAI
