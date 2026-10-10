import OAI.NumberTheory.TotientAsymptotic.IntervalOmegaMoment
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! Uniform quadratic control of the Euler factors for interval moments. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma interval_euler_log_factor {a : ℝ} (ha : 0≤a) (ha' : a≤3/2)
    {p : ℕ} (hp : p.Prime) :
    Real.log ((1-a/(p:ℝ))⁻¹) ≤ a/(p:ℝ)+9/(p:ℝ)^2 := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ)<p := by linarith
  have hx0 : 0≤a/(p:ℝ) := div_nonneg ha hp0.le
  have hx : a/(p:ℝ)≤3/4 := (div_le_iff₀ hp0).mpr (by nlinarith)
  have hTaylor := Real.abs_log_sub_add_sum_range_le
    (show |a/(p:ℝ)|<1 by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    zero_add,pow_one,div_one,abs_of_nonneg hx0] at hTaylor
  have hquad : (a/(p:ℝ))^2/(1-a/(p:ℝ)) ≤ 9/(p:ℝ)^2 := by
    have hden : (1/4:ℝ)≤1-a/(p:ℝ) := by linarith
    calc
      _ ≤ (a/(p:ℝ))^2/(1/4) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
      _ = 4*a^2/(p:ℝ)^2 := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith
  have hh := (abs_le.mp hTaylor).1
  rw [Real.log_inv]
  linarith

lemma prime_reciprocal_squares_le (N : ℕ) :
    (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,1/(p:ℝ)^2) ≤ 1 := by
  have hs : (Finset.Icc 2 N).filter Nat.Prime ⊆ Finset.Ioo 1 (N+1) := by
    intro p hp
    have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Ioo.mpr ⟨by omega,by omega⟩
  calc
    _ ≤ ∑ p ∈ Finset.Ioo 1 (N+1),1/(p:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => by positivity)
    _ ≤ 1 := by
      have h := sum_Ioo_inv_sq_le (α:=ℝ) 1 (N+1)
      norm_num [one_div] at h ⊢
      exact h

lemma interval_euler_product_bound {a : ℝ} (ha : 0≤a) (ha' : a≤3/2)
    (U T : ℝ) (N : ℕ) :
    (∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
      (1-(if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1)/(p:ℝ))⁻¹) ≤
    Real.exp ((∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,(p:ℝ)⁻¹)+
      (a-1)*(∑ p ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
        (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹)+9) := by
  classical
  let P := (Finset.Icc 2 N).filter Nat.Prime
  let w := fun p : ℕ => if U<(p:ℝ) ∧ (p:ℝ)≤T then a else 1
  have hw (p : ℕ) : 0≤w p ∧ w p≤3/2 := by dsimp [w]; split_ifs <;> constructor <;> linarith
  have hfactor (p : ℕ) (hp : p∈P) : 0<(1-w p/(p:ℝ))⁻¹ := by
    have hp2 : (2:ℝ)≤p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    apply inv_pos.mpr
    have hh : w p/(p:ℝ)<1 := (div_lt_one (by linarith)).mpr (by have := hw p; linarith)
    linarith
  have hsum : (∑ p ∈ P,w p/(p:ℝ)) =
      (∑ p ∈ P,(p:ℝ)⁻¹)+(a-1)*(∑ p ∈ P.filter
        (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹) := by
    have hf : (∑ p ∈ P.filter (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹) =
        ∑ p ∈ P,if U<(p:ℝ) ∧ (p:ℝ)≤T then (p:ℝ)⁻¹ else 0 := Finset.sum_filter _ _
    rw [hf,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [w]
    split_ifs <;> ring
  have hlog : Real.log (∏ p ∈ P,(1-w p/(p:ℝ))⁻¹) ≤
      (∑ p ∈ P,(p:ℝ)⁻¹)+(a-1)*(∑ p ∈ P.filter
        (fun p : ℕ => U<(p:ℝ) ∧ (p:ℝ)≤T),(p:ℝ)⁻¹)+9 := by
    rw [Real.log_prod (fun p hp => (hfactor p hp).ne')]
    calc
      _ ≤ ∑ p ∈ P,(w p/(p:ℝ)+9/(p:ℝ)^2) :=
        Finset.sum_le_sum (fun p hp => interval_euler_log_factor (hw p).1 (hw p).2
          (Finset.mem_filter.mp hp).2)
      _ = (∑ p ∈ P,w p/(p:ℝ))+9*(∑ p ∈ P,1/(p:ℝ)^2) := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ _ := by rw [hsum]; nlinarith [prime_reciprocal_squares_le N]
  exact (Real.log_le_iff_le_exp (Finset.prod_pos hfactor)).mp hlog

end TotientAsymptotic

end

end OAI
