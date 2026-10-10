import OAI.NumberTheory.ShortEgyptian.ListConstruction

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

@[irreducible] def dimM : ℕ := (2*1000+2)*(100+2)
@[irreducible] def dimX : ℕ := dimM+2
@[irreducible] def dimC : ℕ := 4*dimX
noncomputable def scaleM (S : ℝ) : ℕ := ⌊S/Real.log S⌋₊
noncomputable def scaleRho (S : ℝ) : ℝ := Real.exp (-(1/10000:ℝ)*scaleM S)
noncomputable def level (S : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((dimX:ℝ)*S-(1/10000:ℝ)*scaleM S*j)
noncomputable def depth (S : ℝ) : ℕ :=
  ⌈((dimX:ℝ)*S-scaleM S)/((1/10000:ℝ)*scaleM S)⌉₊
noncomputable def levelMultiplier (S : ℝ) (C j : ℕ) : ℕ :=
  if Real.exp S < level S j then C else 1
noncomputable def binaryExponent (S : ℝ) : ℕ := ⌈100000*Real.log S/Real.log 2⌉₊

lemma scaleM_bounds (S : ℝ) (hlog : 1 ≤ Real.log S) (hS : 4*Real.log S ≤ S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧
      (scaleM S:ℝ) ≤ S := by
  have hl : 0 < Real.log S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hf := Nat.sub_one_lt_floor (S/Real.log S)
  have hu := Nat.floor_le (div_nonneg hS0 hl.le)
  have hx : 4 ≤ S/Real.log S := (le_div_iff₀ hl).mpr (by linarith)
  refine ⟨?_,hu,hu.trans (div_le_self hS0 hlog)⟩
  dsimp [scaleM]
  have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
  rw [heq]
  linarith

lemma level_pos (S : ℝ) (j : ℕ) : 0 < level S j := Real.exp_pos _
lemma scaleRho_pos (S : ℝ) : 0 < scaleRho S := Real.exp_pos _
lemma scaleRho_le_one (S : ℝ) : scaleRho S ≤ 1 :=
  Real.exp_le_one_iff.mpr (by have hh : (0:ℝ) ≤ scaleM S := Nat.cast_nonneg _; nlinarith)

lemma level_succ (S : ℝ) (j : ℕ) : level S (j+1) = level S j*scaleRho S := by
  unfold level scaleRho
  rw [←Real.exp_add]
  congr 1
  push_cast
  ring

lemma level_antitone (S : ℝ) : Antitone (level S) := by
  apply antitone_nat_of_succ_le
  intro j
  rw [level_succ]
  exact mul_le_of_le_one_right (level_pos S j).le (scaleRho_le_one S)

lemma level_zero (S : ℝ) : level S 0 = Real.exp ((dimX:ℝ)*S) := by simp [level]

lemma level_before_depth (S : ℝ) (hm : 0 < scaleM S) (j : ℕ) :
    j < depth S ↔ Real.exp (scaleM S:ℝ) < level S j := by
  have hmR : 0 < (scaleM S:ℝ) := by exact_mod_cast hm
  rw [depth,Nat.lt_ceil,lt_div_iff₀ (by positivity : (0:ℝ)<(1/10000:ℝ)*scaleM S)]
  unfold level
  rw [Real.exp_lt_exp]
  constructor <;> intro h <;> nlinarith

lemma depth_level (S : ℝ) (hm : 0 < scaleM S) (hmS : (scaleM S:ℝ) ≤ S) :
    level S (depth S) ≤ Real.exp (scaleM S:ℝ) ∧
      Real.exp ((9999/10000:ℝ)*scaleM S) ≤ level S (depth S) := by
  have hmR : 0 < (scaleM S:ℝ) := by exact_mod_cast hm
  have hD : (2:ℝ) ≤ dimX := by norm_num [dimX,dimM]
  have hnum : 0 ≤ (dimX:ℝ)*S-scaleM S := by nlinarith
  have hlo := Nat.le_ceil (((dimX:ℝ)*S-scaleM S)/((1/10000:ℝ)*scaleM S))
  have hhi := Nat.ceil_lt_add_one (div_nonneg hnum (by positivity : (0:ℝ)≤(1/10000:ℝ)*scaleM S))
  have hlo' := (div_le_iff₀ (by positivity : (0:ℝ)<(1/10000:ℝ)*scaleM S)).mp hlo
  have hhi' := mul_lt_mul_of_pos_right hhi (by positivity : (0:ℝ)<(1/10000:ℝ)*scaleM S)
  rw [add_mul,div_mul_cancel₀ _ (by positivity : (1/10000:ℝ)*(scaleM S:ℝ) ≠ 0)] at hhi'
  constructor <;> apply Real.exp_le_exp.mpr <;> dsimp [level,depth] at * <;> nlinarith

lemma depth_bound (S : ℝ) (hS : 0 < S) (hlog : 1 ≤ Real.log S)
    (hm : S/(2*Real.log S) ≤ (scaleM S:ℝ)) (hmS : (scaleM S:ℝ) ≤ S) :
    (depth S:ℝ) ≤ (3*(dimX:ℝ)*10000)*Real.log S := by
  have hl : 0 < Real.log S := by linarith
  have hm0 : 0 < (scaleM S:ℝ) := (div_pos hS (by positivity)).trans_le hm
  have hD : (2:ℝ) ≤ dimX := by norm_num [dimX,dimM]
  have hnum : 0 ≤ (dimX:ℝ)*S-scaleM S := by nlinarith
  have hh := Nat.ceil_lt_add_one (div_nonneg hnum (by positivity : (0:ℝ)≤(1/10000:ℝ)*scaleM S))
  have hSm := (div_le_iff₀ (by positivity : (0:ℝ)<2*Real.log S)).mp hm
  have hdiv : ((dimX:ℝ)*S-scaleM S)/((1/10000:ℝ)*scaleM S) ≤
      2*(dimX:ℝ)*10000*Real.log S := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hSm (by positivity : (0:ℝ)≤dimX)]
  change (⌈_⌉₊:ℝ) ≤ _
  nlinarith

lemma levelMultiplier_pos (S : ℝ) (C j : ℕ) (hC : 0 < C) : 0 < levelMultiplier S C j := by
  unfold levelMultiplier
  split <;> omega

lemma levelMultiplier_dvd (S : ℝ) (C j : ℕ) :
    levelMultiplier S C (j+1) ∣ levelMultiplier S C j := by
  unfold levelMultiplier
  split_ifs with h₁ h₂ h₂
  · exact dvd_refl _
  · exact False.elim (h₂ (h₁.trans_le (level_antitone S (by omega))))
  · exact one_dvd _
  · exact dvd_refl _

lemma levelMultiplier_last (S : ℝ) (C : ℕ) (hm : 0 < scaleM S)
    (hmS : (scaleM S:ℝ) ≤ S) : levelMultiplier S C (depth S) = 1 := by
  apply ite_eq_right
  exact not_lt.mpr ((depth_level S hm hmS).1.trans (Real.exp_le_exp.mpr hmS))

lemma binary_power_lower (S : ℝ) (hS : 0 < S) : S^100000 ≤ (2:ℝ)^binaryExponent S := by
  have hh := Nat.le_ceil (100000*Real.log S/Real.log 2)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh' := (div_le_iff₀ hl).mp hh
  have he : (2:ℝ)^binaryExponent S = Real.exp ((binaryExponent S:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [←Real.exp_log (pow_pos hS 100000),Real.log_pow,he]
  exact Real.exp_le_exp.mpr (by simpa only [binaryExponent,Nat.cast_ofNat] using hh')

lemma binary_power_upper (S : ℝ) (hlog : 1 ≤ Real.log S)
    (hS : 100001*Real.log S ≤ S) : (2:ℝ)^binaryExponent S ≤ Real.exp S := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ 100000*Real.log S) hl2.le)
  have hh' := mul_lt_mul_of_pos_right hh hl2
  rw [add_mul,div_mul_cancel₀ _ hl2.ne',one_mul] at hh'
  have hl2hi : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); norm_num at hh ⊢; exact hh
  have he : (2:ℝ)^binaryExponent S = Real.exp ((binaryExponent S:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [he]
  exact Real.exp_le_exp.mpr (by dsimp [binaryExponent]; nlinarith)

end ShortEgyptian

end OAI
