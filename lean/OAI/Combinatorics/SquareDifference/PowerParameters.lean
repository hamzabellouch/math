import OAI.Combinatorics.SquareDifference.IntervalCrude

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

noncomputable def sourceBeta : ℝ := 1/100000

noncomputable def sourceGamma : ℝ := 1/64

noncomputable def sourceTau (d : ℕ) : ℝ := sourceBeta*sourceGamma/(1000*((d:ℝ)+1))

noncomputable def sourceSigma (d : ℕ) : ℝ := sourceGamma*sourceTau d/4

noncomputable def sourceLoss (d : ℕ) : ℝ := sourceGamma*sourceTau d/(100*((d:ℝ)+1))

noncomputable def powerCutoff (N : ℕ) (a : ℝ) : ℕ := ⌊(N:ℝ)^a⌋₊

noncomputable def childLength (N D : ℕ) : ℕ := ⌈(N:ℝ)/(D:ℝ)^2⌉₊

lemma sourceBeta_pos : 0<sourceBeta := by norm_num [sourceBeta]

lemma sourceBeta_le : sourceBeta≤1 := by norm_num [sourceBeta]

lemma sourceGamma_pos : 0<sourceGamma := by norm_num [sourceGamma]

lemma sourceTau_pos (d : ℕ) : 0<sourceTau d := by
  unfold sourceTau
  exact div_pos (mul_pos sourceBeta_pos sourceGamma_pos) (by positivity)

lemma sourceTau_le (d : ℕ) : sourceTau d≤ sourceBeta*sourceGamma/1000 := by
  unfold sourceTau
  apply div_le_div_of_nonneg_left (mul_nonneg sourceBeta_pos.le sourceGamma_pos.le) (by norm_num)
  nlinarith [Nat.cast_nonneg (α:=ℝ) d]

lemma sourceTau_lt_quarter (d : ℕ) : sourceTau d<1/4 :=
  (sourceTau_le d).trans_lt (by norm_num [sourceBeta,sourceGamma])

lemma sourceSigma_pos (d : ℕ) : 0<sourceSigma d := by
  unfold sourceSigma; exact div_pos (mul_pos sourceGamma_pos (sourceTau_pos d)) (by norm_num)

lemma sourceLoss_pos (d : ℕ) : 0<sourceLoss d := by
  unfold sourceLoss; exact div_pos (mul_pos sourceGamma_pos (sourceTau_pos d)) (by positivity)

lemma source_exponent_gap (d : ℕ) :
    sourceTau d+(d:ℝ)*sourceLoss d+sourceSigma d<sourceBeta*sourceGamma/2 := by
  have ht := sourceTau_pos d
  have hd : 0≤(d:ℝ) := Nat.cast_nonneg _
  have hden : 0<100*((d:ℝ)+1) := by positivity
  have hl : (d:ℝ)*sourceLoss d≤ sourceTau d/100 := by
    unfold sourceLoss
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<100)).mpr
    rw [show (d:ℝ)*(sourceGamma*sourceTau d/(100*((d:ℝ)+1)))*100=
        sourceGamma*sourceTau d*((d:ℝ)/((d:ℝ)+1)) by field_simp]
    have hf : (d:ℝ)/((d:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ ≤ sourceGamma*sourceTau d := by
        exact mul_le_of_le_one_right (mul_nonneg sourceGamma_pos.le ht.le) hf
      _ ≤ sourceTau d := by unfold sourceGamma; linarith
  have hs : sourceSigma d≤ sourceTau d/4 := by unfold sourceSigma sourceGamma; linarith
  have hb := sourceTau_le d
  have hp : 0<sourceBeta*sourceGamma := mul_pos sourceBeta_pos sourceGamma_pos
  linarith

lemma eventually_rpow_dominate (C a b : ℝ) (hab : a<b) :
    ∀ᶠ N : ℕ in atTop,C*(N:ℝ)^a≤(N:ℝ)^b := by
  have h := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  filter_upwards [h,eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  calc
    _ ≤ (N:ℝ)^(b-a)*(N:ℝ)^a := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by rw [←Real.rpow_add hN0]; congr 1; ring

lemma powerCutoff_le (N : ℕ) (a : ℝ) : (powerCutoff N a:ℝ)≤(N:ℝ)^a :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma powerCutoff_mono (N L : ℕ) (a b : ℝ) (h : (N:ℝ)^a≤(L:ℝ)^b) :
    powerCutoff N a≤powerCutoff L b := Nat.floor_mono h

lemma powerCutoff_pos (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : 0≤a) : 0<powerCutoff N a := by
  exact Nat.floor_pos.mpr (Real.one_le_rpow (by exact_mod_cast hN) ha)

lemma powerCutoff_le_self (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : a≤1) : powerCutoff N a≤N := by
  have hh := (powerCutoff_le N a).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) ha)
  rw [Real.rpow_one] at hh
  exact_mod_cast hh

lemma powerCutoff_lower (N : ℕ) (a : ℝ) (h : 2≤(N:ℝ)^a) :
    (N:ℝ)^a/2≤(powerCutoff N a:ℝ) := by
  have hf := Nat.lt_floor_add_one ((N:ℝ)^a)
  change (N:ℝ)^a<(powerCutoff N a:ℝ)+1 at hf
  linarith

lemma childLength_pos (N D : ℕ) (hN : 0<N) (hD : 0<D) : 0<childLength N D := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast hN) (pow_pos (by exact_mod_cast hD) _)

lemma childLength_lower (N D : ℕ) : (N:ℝ)/(D:ℝ)^2≤(childLength N D:ℝ) := Nat.le_ceil _

lemma childLength_cover (N D : ℕ) (hD : 0<D) : N≤D^2*childLength N D := by
  have h := (div_le_iff₀ (pow_pos (show (0:ℝ)<D by exact_mod_cast hD) 2)).mp (childLength_lower N D)
  have hh : (N:ℝ)≤(D:ℝ)^2*(childLength N D:ℝ) := by simpa only [mul_comm] using h
  exact_mod_cast hh

lemma childLength_lt (N D : ℕ) (hN : 2≤N) (hD : 2≤D) : childLength N D<N := by
  have h0 : 0≤(N:ℝ)/(D:ℝ)^2 := by positivity
  have h := Nat.ceil_lt_add_one h0
  have hD4 : (4:ℝ)≤(D:ℝ)^2 := by
    have hd : (2:ℝ)≤D := by exact_mod_cast hD
    nlinarith
  have hd := div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) N) (by norm_num : (0:ℝ)<4) hD4
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hh : (childLength N D:ℝ)<N := by dsimp only [childLength]; linarith
  exact_mod_cast hh

lemma childLength_factor (N D : ℕ) (hN : 0<N) (hD : 0<D) :
    1≤(D:ℝ)^2*(childLength N D:ℝ)/N ∧
      (D:ℝ)^2*(childLength N D:ℝ)/N<1+(D:ℝ)^2/N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hd : (0:ℝ)<(D:ℝ)^2 := pow_pos (by exact_mod_cast hD) _
  constructor
  · apply (le_div_iff₀ hn).mpr
    simpa only [one_mul] using (show (N:ℝ)≤(D:ℝ)^2*(childLength N D:ℝ) by exact_mod_cast childLength_cover N D hD)
  · have hh := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (show 0≤(N:ℝ)/(D:ℝ)^2 by positivity)) hd
    change (D:ℝ)^2*(childLength N D:ℝ)<(D:ℝ)^2*((N:ℝ)/(D:ℝ)^2+1) at hh
    apply (div_lt_iff₀ hn).mpr
    convert hh using 1; field_simp

end SquareDifference

end

end OAI
