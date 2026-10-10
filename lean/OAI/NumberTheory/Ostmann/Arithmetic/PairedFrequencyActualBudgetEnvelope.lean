import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyActualBudgetBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.PairedFrequencyActualBudget
open Conclusion Characters

def nodeConstant (C D A : ℝ) : ℝ := Real.log (max (4*C*D^2) 1*(1+A)^3)

def nodeExponent (C D ε δ A m : ℝ) : ℝ :=
  nodeConstant C D A+(2*δ+2*ε)*A*m+6*Real.sqrt m

theorem nodeConstant_nonneg {C D A : ℝ} (hA : 0 ≤ A) : 0 ≤ nodeConstant C D A := by
  apply Real.log_nonneg
  have hp : (1:ℝ) ≤ (1+A)^3 := one_le_pow₀ (by linarith)
  exact one_le_mul_of_one_le_of_one_le (le_max_right _ _) hp

private theorem self_le_exp_two_sqrt {m : ℝ} (hm : 0 < m) :
    m ≤ Real.exp (2*Real.sqrt m) := by
  have hl := Real.log_le_rpow_div hm.le (by norm_num : (0:ℝ)<1/2)
  rw [←Real.sqrt_eq_rpow] at hl
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hm] at he
  convert he using 1
  congr 1
  ring

theorem nodeBudget_le_exp {C D ε δ A m : ℝ} (_hC : 0 ≤ C) (_hD : 0<D)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hm : 1  ≤  m)
    (V : List Bool→ℕ) (hV : ∀p,1 ≤ V p)
    (hb : ∀p,(V p:ℝ) ≤ Real.exp (A*m)) (p : List Bool) :
    PairedFrequencyTreeSum.nodeBudget C D ε δ V p ≤ Real.exp (nodeExponent C D ε δ A m) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hv0 : (0:ℝ)<V p := by exact_mod_cast hV p
  have hv1 : (1:ℝ) ≤ V p := by exact_mod_cast hV p
  have hlog : Real.log (V p) ≤ A*m := by
    simpa only [Real.log_exp] using Real.log_le_log hv0 (hb p)
  have hlog0 : 0 ≤ 1+Real.log (V p) := add_nonneg zero_le_one (Real.log_nonneg hv1)
  have hp : 1+Real.log (V p) ≤ (1+A)*Real.exp (2*Real.sqrt m) := by
    calc
      _ ≤ (1+A)*m := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (self_le_exp_two_sqrt hm0) (by positivity)
  have hr (s : List Bool) (t : ℝ) (ht : 0 ≤ t) :
      (V s:ℝ)^t ≤ Real.exp (t*A*m) := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg _) (hb s) ht
    rw [←Real.exp_mul] at h
    convert h using 1
    congr 1
    ring
  have hp3 := pow_le_pow_left₀ hlog0 hp 3
  have hfour : 4*C*D^2*(V (false::p):ℝ)^δ*(V (true::p):ℝ)^δ*(V p:ℝ)^(2*ε) ≤ 
      max (4*C*D^2) 1*Real.exp (δ*A*m)*Real.exp (δ*A*m)*Real.exp ((2*ε)*A*m) := by
    apply mul_le_mul _ (hr _ _ (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
    apply mul_le_mul _ (hr _ _ hδ) (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
    exact mul_le_mul (le_max_left _ _) (hr _ _ hδ)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  calc
    _ ≤ max (4*C*D^2) 1*Real.exp (δ*A*m)*Real.exp (δ*A*m)*Real.exp ((2*ε)*A*m)*
        ((1+A)*Real.exp (2*Real.sqrt m))^3 :=
      mul_le_mul hfour hp3 (pow_nonneg hlog0 _) (by positivity)
    _=Real.exp (nodeExponent C D ε δ A m) := by
      rw [mul_pow,←Real.exp_nat_mul]
      unfold nodeExponent nodeConstant
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by positivity)]
      rw [show (2*δ+2*ε)*A*m=δ*A*m+δ*A*m+(2*ε)*A*m by ring,
        Real.exp_add,Real.exp_add]
      have he : (3:ℝ)*(2*Real.sqrt m)=6*Real.sqrt m := by ring
      norm_num only [Nat.cast_ofNat]
      rw [he]
      ring

theorem paired_leaf_card_le (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ)
    (p : List Bool) (hp : p.length=l) :
    ((pairedRanges Bs BD Bz k L l p).card:ℝ) ≤ 
      Real.exp (2*initialGap Bs k L+2*Real.sqrt (bulkSize k L)+2*Real.log 2) := by
  have hf : (addressBound Bs BD Bz k L l p:ℝ) ≤ 
      Real.exp (initialGap Bs k L+Real.sqrt (bulkSize k L)) := by
    unfold addressBound frequencyBound
    simpa [hp,frequencyBudget] using
      (Nat.floor_le (Real.exp_pos (frequencyBudget Bs BD Bz k L 0)).le)
  rw [pairedRanges_card,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
  calc
    _ ≤ (2*Real.exp (initialGap Bs k L+Real.sqrt (bulkSize k L)))^2 := by gcongr
    _=_ := by
      rw [mul_pow,←Real.exp_nat_mul]
      rw [show 2*initialGap Bs k L+2*Real.sqrt (bulkSize k L)+2*Real.log 2=
        2*Real.log 2+2*(initialGap Bs k L+Real.sqrt (bulkSize k L)) by ring,
        Real.exp_add]
      have he (t : ℝ) : Real.exp (2*t)=(Real.exp t)^2 := by
        rw [show 2*t=t+t by ring,Real.exp_add,pow_two]
      norm_num only [Nat.cast_ofNat]
      rw [he,he,Real.exp_log (by norm_num : (0:ℝ)<2)]
      norm_num

end Ostmann.Arithmetic.PairedFrequencyActualBudget

end

end OAI
