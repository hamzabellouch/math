import Mathlib.Analysis.MeanInequalities

namespace OAI

/-! # The equal-exponent finite Hölder inequality for coordinate deletion

This is the finite sum inequality needed in the induction proving the exact
lattice Loomis–Whitney input. It follows from weighted arithmetic–geometric
mean after normalizing each row by its actual sum.
-/
namespace Falconer
open scoped BigOperators

variable {ι α : Type*}

theorem finite_holder_equal (I : Finset ι) (B : Finset α) (hI : I.Nonempty)
    (f : ι → α → ℝ) (hf : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ f i x) :
    (∑ x ∈ B, ∏ i ∈ I, (f i x) ^ (1/(I.card:ℝ))) ≤
      ∏ i ∈ I, (∑ x ∈ B, f i x) ^ (1/(I.card:ℝ)) := by
  classical
  let p : ℝ := 1/(I.card:ℝ)
  let M : ι → ℝ := fun i => ∑ x ∈ B, f i x
  have hcard : 0 < (I.card:ℝ) := by exact_mod_cast hI.card_pos
  have hp : 0 < p := one_div_pos.mpr hcard
  have hweights : ∑ _i ∈ I, p = 1 := by
    simp only [Finset.sum_const,nsmul_eq_mul,p]
    exact mul_one_div_cancel hcard.ne'
  have hMnonneg : ∀ i ∈ I, 0 ≤ M i := fun i hi =>
    Finset.sum_nonneg (fun x hx => hf i hi x hx)
  by_cases hM : ∀ i ∈ I, 0 < M i
  · let g : ι → α → ℝ := fun i x => f i x / M i
    have hg : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ g i x :=
      fun i hi x hx => div_nonneg (hf i hi x hx) (hMnonneg i hi)
    have hgsum : ∀ i ∈ I, ∑ x ∈ B, g i x = 1 := by
      intro i hi
      simp only [g,← Finset.sum_div,M]
      exact div_self (hM i hi).ne'
    have hmean : ∀ x ∈ B, (∏ i ∈ I, (g i x)^p) ≤ ∑ i ∈ I, p*g i x := by
      intro x hx
      exact Real.geom_mean_le_arith_mean_weighted I (fun _ => p) (fun i => g i x)
        (fun _ _ => hp.le) hweights (fun i hi => hg i hi x hx)
    have hsum : (∑ x ∈ B, ∏ i ∈ I, (g i x)^p) ≤ 1 := by
      calc
        _ ≤ ∑ x ∈ B, ∑ i ∈ I, p*g i x := Finset.sum_le_sum hmean
        _ = ∑ i ∈ I, p*(∑ x ∈ B, g i x) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
        _ = 1 := by
          calc
            _ = ∑ i ∈ I, p := Finset.sum_congr rfl (fun i hi => by rw [hgsum i hi,mul_one])
            _ = 1 := hweights
    have hprod : ∀ x ∈ B, (∏ i ∈ I, (f i x)^p) =
        (∏ i ∈ I, (M i)^p)*(∏ i ∈ I, (g i x)^p) := by
      intro x hx
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      change (f i x)^p = (M i)^p*(f i x/M i)^p
      rw [Real.div_rpow (hf i hi x hx) (hMnonneg i hi)]
      have hne : (M i)^p ≠ 0 := (Real.rpow_pos_of_pos (hM i hi) _).ne'
      field_simp
    change (∑ x ∈ B, ∏ i ∈ I, (f i x)^p) ≤ ∏ i ∈ I, (M i)^p
    calc
      _ = (∏ i ∈ I, (M i)^p)*(∑ x ∈ B, ∏ i ∈ I, (g i x)^p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hprod
      _ ≤ (∏ i ∈ I, (M i)^p)*1 :=
        mul_le_mul_of_nonneg_left hsum (Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (hMnonneg i hi) _))
      _ = _ := mul_one _
  · push Not at hM
    obtain ⟨i,hi,hMi⟩ := hM
    have hzero : M i = 0 := le_antisymm hMi (hMnonneg i hi)
    have hrow : ∀ x ∈ B, f i x = 0 := by
      intro x hx
      apply le_antisymm _ (hf i hi x hx)
      calc
        f i x ≤ ∑ y ∈ B, f i y := Finset.single_le_sum (fun y hy => hf i hi y hy) hx
        _ = 0 := hzero
    have hleft : (∑ x ∈ B, ∏ j ∈ I, (f j x)^p) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply Finset.prod_eq_zero hi
      rw [hrow x hx,Real.zero_rpow hp.ne']
    change (∑ x ∈ B, ∏ i ∈ I, (f i x)^p) ≤ ∏ i ∈ I, (M i)^p
    rw [hleft]
    exact Finset.prod_nonneg (fun j hj => Real.rpow_nonneg (hMnonneg j hj) _)

end Falconer

end OAI
