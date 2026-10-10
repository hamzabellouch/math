import OAI.Analysis.LipschitzHilbert.Trees.SourceParameters

namespace OAI

/-! Taking the manuscript exponent p=sqrt L absorbs the fixed polynomial
weight and stopping costs in the integrated vertex estimate. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_vertex_constant_budget (q A B K : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ α : ℝ, 1 ≤ α → α ≤ 3 →
      let cost := 1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1)
      (cost*(1+K*L^B*cost))^(1/Real.sqrt L) ≤ L^(2*q+1) := by
  filter_upwards [eventually_ge_atTop (max 1 (64*(1+K))),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (4*A+B+1)] with L hLbig hp
  intro α hα hα3
  dsimp only
  have hL : 1 ≤ L := (le_max_left _ _).trans hLbig
  have hLc : 64*(1+K) ≤ L := (le_max_right _ _).trans hLbig
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  let X := (L^q)^(Real.sqrt L)
  let Y := L^A
  let cost := 1+X*(Y+1)^(α-1)
  have hX : 1 ≤ X := Real.one_le_rpow (Real.one_le_rpow hL hq) hp0.le
  have hY : 1 ≤ Y := Real.one_le_rpow hL hA
  have hLB : 1 ≤ L^B := Real.one_le_rpow hL hB
  have hY2 : 1 ≤ Y^2 := one_le_pow₀ hY
  have hpow : (Y+1)^(α-1) ≤ 4*Y^2 := by
    calc
      _ ≤ (Y+1)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (Y+1)^2 := Real.rpow_two _
      _ ≤ 4*Y^2 := by nlinarith
  have hXY : 1 ≤ X*Y^2 := one_le_mul_of_one_le_of_one_le hX hY2
  have hcost : cost ≤ 8*X*Y^2 := by
    have h := mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hX)
    dsimp only [cost]
    nlinarith
  have hcost0 : 0 ≤ cost := by dsimp [cost]; positivity
  have hnext : 1+K*L^B*cost ≤ (1+K)*L^B*(8*X*Y^2) := by
    have hb : 1 ≤ L^B*(8*X*Y^2) :=
      one_le_mul_of_one_le_of_one_le hLB (by nlinarith)
    have hk := mul_le_mul_of_nonneg_left hcost (show 0 ≤ K*L^B by positivity)
    nlinarith
  have htotal : cost*(1+K*L^B*cost) ≤
      64*(1+K)*L^B*X^2*Y^4 := by
    have h := mul_le_mul hcost hnext (by positivity : 0 ≤ 1+K*L^B*cost)
      (by positivity : 0 ≤ 8*X*Y^2)
    nlinarith
  have hpower : L^B*X^2*Y^4 = L^(2*q*Real.sqrt L+4*A+B) := by
    dsimp only [X,Y]
    rw [← Real.rpow_natCast,← Real.rpow_mul (Real.rpow_nonneg hL0.le _),
      ← Real.rpow_mul hL0.le,← Real.rpow_natCast,← Real.rpow_mul hL0.le,
      ← Real.rpow_add hL0,← Real.rpow_add hL0]
    congr 1
    push_cast
    ring
  have hbase : cost*(1+K*L^B*cost) ≤ L^((2*q+1)*Real.sqrt L) := by
    calc
      _ ≤ 64*(1+K)*(L^B*X^2*Y^4) := by nlinarith [htotal]
      _ ≤ L*(L^B*X^2*Y^4) := mul_le_mul_of_nonneg_right hLc (by positivity)
      _ = L^(2*q*Real.sqrt L+4*A+B+1) := by
        rw [hpower]
        calc
          _ = L^(2*q*Real.sqrt L+4*A+B)*L^(1:ℝ) := by rw [Real.rpow_one]; ring
          _ = _ := (Real.rpow_add hL0 _ _).symm
      _ ≤ L^((2*q+1)*Real.sqrt L) :=
        Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ cost*(1+K*L^B*cost)) hbase
    (one_div_nonneg.mpr hp0.le)
  have heq : (L^((2*q+1)*Real.sqrt L))^(1/Real.sqrt L) = L^(2*q+1) := by
    rw [← Real.rpow_mul hL0.le]
    congr 1
    field_simp
  exact h.trans_eq heq

theorem eventually_source_vertex_moment_budget (q A B K : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ α E S : ℝ, 1 ≤ α → α ≤ 3 → 0 ≤ E → 0 ≤ S →
      let cost := 1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1)
      E ≤ cost*(1+K*L^B*cost)*S →
      E^(1/Real.sqrt L) ≤ L^(2*q+1)*S^(1/Real.sqrt L) := by
  filter_upwards [eventually_source_vertex_constant_budget q A B K hq hA hB hK,
    eventually_ge_atTop (1:ℝ)] with L hbudget hL
  intro α E S hα hα3 hE hS
  dsimp only
  intro henergy
  have hp : 0 ≤ 1/Real.sqrt L := by positivity
  have hcost : 0 ≤ (1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1))*
      (1+K*L^B*(1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1))) := by positivity
  calc
    E^(1/Real.sqrt L) ≤
        ((1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1))*
        (1+K*L^B*(1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1)))*S)^(1/Real.sqrt L) :=
      Real.rpow_le_rpow hE henergy hp
    _ = ((1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1))*
        (1+K*L^B*(1+(L^q)^(Real.sqrt L)*(L^A+1)^(α-1))))^(1/Real.sqrt L)*
        S^(1/Real.sqrt L) := Real.mul_rpow hcost hS
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbudget α hα hα3) (Real.rpow_nonneg hS _)

end LipschitzHilbert

end

end OAI
