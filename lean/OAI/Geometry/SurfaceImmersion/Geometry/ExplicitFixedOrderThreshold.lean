import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPowerThreshold

namespace OAI

/-! The fixed-order scale conditions with one explicitly specified
threshold. Its reciprocal is polynomial in the finite numerical budgets. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.ExactCorrection

def fixedOrderNumericalBudget (k : ℕ) (D B K : ℝ) (C : ℕ → ℝ) : ℝ :=
  2+D*B+K+∑ m ∈ Finset.range (k/2+1), |C m|

def fixedOrderThreshold (k : ℕ) (ρ a η D B K : ℝ) (C : ℕ → ℝ) : ℝ :=
  powerThreshold 10 (fixedOrderNumericalBudget k D B K C) (min η (min (ρ/4) (a/8)))

theorem fixedOrderThreshold_spec (k : ℕ) (hk : 10 ≤ k)
    (ρ a η D B K : ℝ) (hρ : 0 < ρ) (ha : 0 < a) (hη : 0 < η)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hK : 0 ≤ K) (C : ℕ → ℝ) :
    0 < fixedOrderThreshold k ρ a η D B K C ∧
    fixedOrderThreshold k ρ a η D B K C ≤ 1 ∧
    ∀ t : ℝ, 0 < t → t < fixedOrderThreshold k ρ a η D B K C →
    ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      t^(6/5 : ℝ)/t^(11/10 : ℝ) ≤ η ∧
      D*B*(t^(11/10 : ℝ)/t)^(40*(k+1)) ≤ min (ρ/4) (a/8) ∧
      (t^((6/5 : ℝ)*(j : ℝ))/t^(k : ℝ))^(2 : ℕ)*K ≤ a/8 ∧
      (∀ m ≤ k/2, C m*(t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m ≤ ρ*t) ∧
      t^((6/5 : ℝ)*(j : ℝ)) ≤ t^(k : ℝ) ∧
      t^((6/5 : ℝ)*((k : ℝ)+1)) ≤ t^((6/5 : ℝ)*(j : ℝ)) := by
  let M := 1+∑ m ∈ Finset.range (k/2+1), |C m|
  let S := fixedOrderNumericalBudget k D B K C
  let b := min η (min (ρ/4) (a/8))
  have hsum : 0 ≤ ∑ m ∈ Finset.range (k/2+1), |C m| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hDB := mul_nonneg hD hB
  have hS : 0 ≤ S := by dsimp [S, fixedOrderNumericalBudget]; linarith
  have hS1 : 1 ≤ S := by dsimp [S, fixedOrderNumericalBudget]; linarith
  have hSDB : D*B ≤ S := by dsimp [S, fixedOrderNumericalBudget]; linarith
  have hSK : K ≤ S := by dsimp [S, fixedOrderNumericalBudget]; linarith
  have hSM : M ≤ S := by dsimp [S, fixedOrderNumericalBudget, M]; linarith
  have hb : 0 < b := lt_min hη (lt_min (by positivity) (by positivity))
  have hε := powerThreshold_spec (n := 10) (by decide) hS hb
    (show ((10 : ℕ) : ℝ)⁻¹ ≤ (1/10 : ℝ) by norm_num)
  refine ⟨hε.1,hε.2.1,?_⟩
  intro t ht htε j hkj hjk
  have ht1 : t ≤ 1 := htε.le.trans hε.2.1
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
  have hjk' : (j : ℝ) ≤ (k : ℝ)+1 := by exact_mod_cast hjk
  have hbound (c p : ℝ) (hc : c ≤ S) (hp : (1/10 : ℝ) ≤ p) : c*t^p ≤ b := by
    have hh := (powerThreshold_spec (n := 10) (by decide) hS hb
      (show ((10 : ℕ) : ℝ)⁻¹ ≤ p by norm_num; exact hp)).2.2 t ht htε
    exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg ht.le _)).trans hh.le
  have hr : t^(6/5 : ℝ)/t^(11/10 : ℝ) = t^(1/10 : ℝ) := by
    rw [← Real.rpow_sub ht]
    norm_num
  have hs : t^(11/10 : ℝ)/t = t^(1/10 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_sub ht]
    norm_num
  have hpow : (t^(11/10 : ℝ)/t)^(40*(k+1)) = t^(4*((k : ℝ)+1)) := by
    rw [hs,← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring
  have hδ : (t^((6/5 : ℝ)*(j : ℝ))/t^(k : ℝ))^(2 : ℕ) =
      t^((12/5 : ℝ)*(j : ℝ)-2*(k : ℝ)) := by
    rw [← Real.rpow_sub ht,← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    ring
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr]
    have hh := hbound 1 (1/10) hS1 le_rfl
    simpa only [one_mul] using hh.trans (min_le_left _ _)
  · rw [hpow]
    exact (hbound (D*B) _ hSDB (by linarith)).trans (min_le_right _ _)
  · rw [hδ,mul_comm]
    exact (hbound K _ hSK (by linarith)).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  · intro m hm
    have hCM : C m ≤ M := by
      have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (k/2+1)) => abs_nonneg (C j))
        (Finset.mem_range.mpr (by omega : m < k/2+1))
      have hc := le_abs_self (C m)
      dsimp [M]
      linarith
    let e : ℝ := (k : ℝ)+(1/5 : ℝ)-(6/5 : ℝ)*(m : ℝ)
    have hmk : 2*m ≤ k := by omega
    have hmk' : (2 : ℝ)*(m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have he : (1/10 : ℝ) ≤ e := by dsimp [e]; linarith
    have heρ : C m*t^e ≤ ρ := (hbound (C m) e (hCM.trans hSM) he).trans (by
      have hbρ : b ≤ ρ/4 := (min_le_right _ _).trans (min_le_left _ _)
      linarith)
    have hratio : (t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m = t^e*t := by
      rw [← Real.rpow_natCast,← Real.rpow_mul ht.le,scale_quotient_product ht]
      conv_rhs => rhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      dsimp [e]
      ring
    calc
      _ = C m*((t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m) := by ring
      _ = (C m*t^e)*t := by rw [hratio]; ring
      _ ≤ ρ*t := mul_le_mul_of_nonneg_right heρ ht.le
  · exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
