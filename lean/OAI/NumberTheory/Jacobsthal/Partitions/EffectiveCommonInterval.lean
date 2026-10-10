import OAI.NumberTheory.Jacobsthal.Primes.SmallEffectivePrimeSplit

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceCommon
open ErdosVarianceEffective ErdosInverseTail ErdosInverseHits

noncomputable def commonLength (Y qf : ℕ) (R xi : ℝ) : ℕ :=
  commonParentLength Y qf ((1+xi)*R)

theorem bin_upper_comparison (R xi : ℝ) (_hR : 0 < R) (hxi : 0 ≤ xi)
    (p : ℕ) (hbin : R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) :
    (p : ℝ) ≤ (1+xi)*R ∧ (1+xi)*R ≤ (1+xi)*(p : ℝ) :=
  ⟨hbin.2,mul_le_mul_of_nonneg_left hbin.1.le (by linarith)⟩

theorem commonLength_le_effective (Y : ℕ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p)
    (R xi : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi)
    (hbin : R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) :
    commonLength Y qf R xi ≤ hitLength Y (p*qf) (effectiveBase a r qf p hHp) := by
  have hb := (effective_initial_bounds a r qf hq p hHp).2
  have hh := commonParentLength_le_hits Y qf p (effectiveBase a r qf p hHp)
    (Nat.pos_of_ne_zero hq.ne_zero) (Nat.pos_of_ne_zero (NeZero.ne p)) (by simpa only [effectiveBase,Nat.mul_comm] using hb)
    ((1+xi)*R) (bin_upper_comparison R xi hR hxi p hbin).1
  simpa only [commonLength,Nat.mul_comm] using hh

theorem commonLength_tail_bound (Y : ℕ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) [NeZero p] (hHp : (effectiveModulus a r qf).Coprime p)
    (R xi : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hbin : R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) :
    ((hitLength Y (p*qf) (effectiveBase a r qf p hHp)-commonLength Y qf R xi : ℕ) : ℝ) ≤
      xi*(commonLength Y qf R xi : ℝ)+3 := by
  have hb := effective_initial_bounds a r qf hq p hHp
  have hcomp := bin_upper_comparison R xi hR hxi p hbin
  have hh := actual_cell_tail_length Y qf p (effectiveBase a r qf p hHp)
    (Nat.pos_of_ne_zero hq.ne_zero) (Nat.pos_of_ne_zero (NeZero.ne p)) hb.1
    (by simpa only [effectiveBase,Nat.mul_comm] using hb.2) ((1+xi)*R) xi hxi hxi1 hcomp.1 hcomp.2
  simpa only [commonLength,Nat.mul_comm] using hh

theorem commonLength_reference_bounds (Y qf p : ℕ) (hq : 0 < qf) (hp : 0 < p)
    (R xi : ℝ) (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hbin : R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) :
    (commonLength Y qf R xi : ℝ) ≤ (Y : ℝ)/((p : ℝ)*qf) ∧
      (Y : ℝ)/((p : ℝ)*qf)-(commonLength Y qf R xi : ℝ) ≤
        xi*(commonLength Y qf R xi : ℝ)+2 := by
  have hqR : (0 : ℝ) < qf := by exact_mod_cast hq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hU : 0 < (1+xi)*R := by positivity
  have hratio : 0 ≤ (Y : ℝ)/((qf : ℝ)*((1+xi)*R)) := by positivity
  have hfloor : (commonLength Y qf R xi : ℝ) ≤ (Y : ℝ)/((qf : ℝ)*((1+xi)*R)) := Nat.floor_le hratio
  have hfloorHi : (Y : ℝ)/((qf : ℝ)*((1+xi)*R)) < (commonLength Y qf R xi : ℝ)+1 := Nat.lt_floor_add_one _
  have hcomp := bin_upper_comparison R xi hR hxi p hbin
  have hdiv : (Y : ℝ)/((qf : ℝ)*((1+xi)*R)) ≤ (Y : ℝ)/((p : ℝ)*qf) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by nlinarith)
  have hinfl : (Y : ℝ)/((p : ℝ)*qf) ≤ (1+xi)*((Y : ℝ)/((qf : ℝ)*((1+xi)*R))) := by
    have hf : ((1+xi)*R)/(p : ℝ) ≤ 1+xi := (div_le_iff₀ hpR).mpr hcomp.2
    calc
      _ = ((Y : ℝ)/((qf : ℝ)*((1+xi)*R)))*(((1+xi)*R)/(p : ℝ)) := by field_simp
      _ ≤ ((Y : ℝ)/((qf : ℝ)*((1+xi)*R)))*(1+xi) := mul_le_mul_of_nonneg_left hf hratio
      _ = _ := by ring
  refine ⟨hfloor.trans hdiv,?_⟩
  have hh := mul_le_mul_of_nonneg_left hfloorHi.le (show 0 ≤ 1+xi by linarith)
  nlinarith

end ErdosVarianceCommon

end

end Erdos970

end OAI
