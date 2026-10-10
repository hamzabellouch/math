import OAI.NumberTheory.Ostmann.Supply.KernelTruncatedWeight
import OAI.NumberTheory.Ostmann.Supply.TruncationScale

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Filter
open scoped BigOperators

theorem supply_tail_le_contracted_unit {L H U : ℝ} (hL : 0≤L) (hH : H≤L)
    (hU : Real.exp (-8*supplyEpsilon*H)≤U) :
    Real.exp (-10*L)≤U*Real.exp (-(8/5:ℝ)*H) := by
  have hc : 0≤8*supplyEpsilon+(8/5:ℝ) := by norm_num [supplyEpsilon]
  have hh := mul_le_mul_of_nonneg_left hH hc
  have he : -10*L≤-8*supplyEpsilon*H-(8/5:ℝ)*H := by
    norm_num only [supplyEpsilon] at hh ⊢
    linarith
  calc
    _ ≤ Real.exp (-8*supplyEpsilon*H-(8/5:ℝ)*H) := Real.exp_le_exp.mpr he
    _ = Real.exp (-8*supplyEpsilon*H)*Real.exp (-(8/5:ℝ)*H) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hU (Real.exp_pos _).le

theorem supply_tail_le_half_unit {L H U : ℝ} (hL : 1≤L) (hH : H≤L)
    (hU : Real.exp (-8*supplyEpsilon*H)≤U) :
    Real.exp (-10*L)≤U/2 := by
  have hh := mul_le_mul_of_nonneg_left hH
    (by norm_num [supplyEpsilon] : 0≤8*supplyEpsilon)
  have he : -10*L≤-8*supplyEpsilon*H-1 := by
    norm_num only [supplyEpsilon] at hh ⊢
    linarith
  have he1 : (2:ℝ)≤Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  calc
    _ ≤ Real.exp (-8*supplyEpsilon*H-1) := Real.exp_le_exp.mpr he
    _ = Real.exp (-8*supplyEpsilon*H)/Real.exp 1 := Real.exp_sub _ _
    _ ≤ Real.exp (-8*supplyEpsilon*H)/2 :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) he1
    _ ≤ U/2 := div_le_div_of_nonneg_right hU (by norm_num)

theorem eventually_kernelTruncation_norm_contracted :
    ∀ᶠL:ℝ in atTop, ∀p:ℕ→ℕ,∀ _hzero:∀i,NeZero (p i),
      ∀S:∀i,Finset (ZMod (p i)),∀n:ℕ,
      (∀i<n,1000≤p i) → (∀i<n,(1/3:ℝ)≤density (S i)) →
      (∀i<n,density (S i)≤2/3) → (∀i<n,gamma (S i)≤ supplyEpsilon^2) →
      reciprocalMass (Finset.range n) p≤L →
      ‖BivariateTruncation.rectangularTruncation (kernelTensorPolynomial p S n) (supplyTruncation L)‖ ≤
        2*kernelUnitProduct (Finset.range n) p S*
          Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p) := by
  filter_upwards [eventually_supply_tail_small,eventually_ge_atTop (0:ℝ)] with L htail hL
  intro p hzero S n hp hlo hhi hg hH
  let : ∀i,NeZero (p i) := hzero
  have hU := (kernelUnitProduct_exp_bounds (Finset.range n) p S
    (fun i hi => by have := hp i (Finset.mem_range.mp hi); omega)
    (fun i hi => hlo i (Finset.mem_range.mp hi))
    (fun i hi => hhi i (Finset.mem_range.mp hi))
    (fun i hi => hg i (Finset.mem_range.mp hi))).1
  have hsmall := (htail _ 3 hH (by norm_num) (by norm_num)).trans
    (supply_tail_le_contracted_unit hL hH hU)
  have hk := kernelTruncation_norm p S n (supplyTruncation L) hp hlo hhi hg
  linarith

theorem eventually_unitWeightMean_comparable {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ᶠL:ℝ in atTop, ∀p:ι→ℕ,∀ _hp:∀i,Fact (p i).Prime,
      ∀S:∀i,Finset (ZMod (p i)),
      (∀i,(1/3:ℝ)≤density (S i)) → (∀i,density (S i)≤2/3) →
      (∀i,gamma (S i)≤ supplyEpsilon^2) → (∑i,1/(p i:ℝ))≤L →
      (∏i,unitKernelMean (S i) sparseKernelScale)/2≤unitWeightMean p S (supplyTruncation L) ∧
      unitWeightMean p S (supplyTruncation L)≤2*(∏i,unitKernelMean (S i) sparseKernelScale) := by
  filter_upwards [eventually_supply_tail_small,eventually_ge_atTop (1:ℝ)] with L htail hL
  intro p hp S hlo hhi hg hH
  let : ∀i,Fact (p i).Prime := hp
  have hU := (kernelUnitProduct_exp_bounds Finset.univ p S
    (fun i _ => (Fact.out : (p i).Prime).two_le)
    (fun i _ => hlo i) (fun i _ => hhi i) (fun i _ => hg i)).1
  have hsmall := (htail _ (8*supplyEpsilon) hH
    (by norm_num [supplyEpsilon]) (by norm_num [supplyEpsilon])).trans
      (supply_tail_le_half_unit hL hH hU)
  have herror := (unitWeightMean_error p S (supplyTruncation L) hlo hhi hg).trans hsmall
  obtain ⟨ha,hb⟩ := abs_le.mp herror
  have hpos : 0≤(∏i,unitKernelMean (S i) sparseKernelScale) :=
    (Real.exp_pos _).le.trans hU
  change _≤(∏i,unitKernelMean (S i) sparseKernelScale)/2 at hb
  change -((∏i,unitKernelMean (S i) sparseKernelScale)/2)≤_ at ha
  constructor <;> linarith

end Ostmann.Supply

end

end OAI
