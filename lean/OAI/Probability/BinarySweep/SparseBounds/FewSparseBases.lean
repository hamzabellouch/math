import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.SparseReduction

namespace OAI

noncomputable section

namespace BinaryCoordinateSweeps.Sparse

lemma few_eta_good (b : ℕ) {L : ℝ} (hb : b ≤ 16000) (hL : (10:ℝ)^26 ≤ L) :
    Real.exp (-L/160000) ≤ 1/4 ∧
    4*(b:ℝ)*Real.sqrt (Real.exp (-L/160000)) ≤ Real.exp (-L/640000) := by
  have hbR : (b:ℝ) ≤ 16000 := by exact_mod_cast hb
  constructor
  · have hc : (4:ℝ) ≤ Real.exp (L/160000) := by
      apply (show (4:ℝ) ≤ L/160000+1 from by linarith).trans (Real.add_one_le_exp _)
    rw [show -L/160000=-(L/160000) by ring,Real.exp_neg]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) hc
  · have hc : 4*(b:ℝ) ≤ Real.exp (L/640000) := by
      apply (show 4*(b:ℝ) ≤ L/640000+1 from by linarith).trans (Real.add_one_le_exp _)
    have hs : Real.sqrt (Real.exp (-L/160000))=Real.exp (-L/320000) := by
      apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)).mpr
      rw [←Real.exp_add]
      congr 1
      ring
    rw [hs]
    refine (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    ring

lemma few_vertex_base (b h k : ℕ) {s : ℝ} (hs : 0<s) (hb : b ≤ 16000)
    (hL : (10:ℝ)^26 ≤ Real.log s) (hk : ((k+h:ℕ):ℝ) ≤ s^(1599/1600:ℝ)) :
    ((k+h:ℕ):ℝ)*((b+1:ℝ)/s) ≤ Real.exp (-Real.log s/3200) := by
  have hbR : (b+1:ℝ) ≤ 16001 := by exact_mod_cast (by omega : b+1 ≤ 16001)
  have hc : (b+1:ℝ) ≤ Real.exp (Real.log s/3200) := by
    apply (show (b+1:ℝ) ≤ Real.log s/3200+1 from by linarith).trans (Real.add_one_le_exp _)
  have hkE : ((k+h:ℕ):ℝ) ≤ Real.exp ((1599/1600:ℝ)*Real.log s) := by
    simpa only [Real.rpow_def_of_pos hs,mul_comm] using hk
  calc
    _  ≤  Real.exp ((1599/1600:ℝ)*Real.log s)*(Real.exp (Real.log s/3200)/s) := by
      exact mul_le_mul hkE (div_le_div_of_nonneg_right hc hs.le) (by positivity) (by positivity)
    _ = _ := by
      rw [←Real.exp_log hs,←Real.exp_sub,←Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring

lemma few_line_base (u h k : ℕ) {s : ℝ} (hs : 0<s)
    (hL : (10:ℝ)^26 ≤ Real.log s) (hk : ((k+h:ℕ):ℝ) ≤ s^(1599/1600:ℝ))
    (hu : u ≤ k+h) :
    2*(u:ℝ)/(s*Real.exp (-Real.log s/160000)) ≤ Real.exp (-Real.log s/3200) := by
  have huE : (u:ℝ) ≤ Real.exp ((1599/1600:ℝ)*Real.log s) := by
    refine (show (u:ℝ) ≤ ((k+h:ℕ):ℝ) by exact_mod_cast hu).trans ?_
    simpa only [Real.rpow_def_of_pos hs,mul_comm] using hk
  have hc : (2:ℝ) ≤ Real.exp ((49/160000:ℝ)*Real.log s) := by
    apply (show (2:ℝ) ≤ (49/160000:ℝ)*Real.log s+1 from by linarith).trans (Real.add_one_le_exp _)
  calc
    _  ≤  (Real.exp ((49/160000:ℝ)*Real.log s)*Real.exp ((1599/1600:ℝ)*Real.log s))/
        (s*Real.exp (-Real.log s/160000)) := by gcongr
    _ = _ := by
      rw [←Real.exp_log hs,←Real.exp_add,←Real.exp_add,←Real.exp_sub]
      simp only [Real.log_exp]
      congr 1
      ring

lemma adaptive_count_small (O k : ℕ) {s m η : ℝ} (hs : 0<s)
    (hL : (10:ℝ)^26 ≤ Real.log s) (hO : (O+1:ℝ) ≤ 2*s) (hm : 8000000000 ≤ m*η) :
    (O+1:ℝ)^⌊2*(k:ℝ)/(m*η)⌋₊ ≤ Real.exp ((k:ℝ)*Real.log s/2000000000) := by
  have hm0 : 0 < m*η := by linarith
  have hlog0 : 0 ≤ Real.log (O+1:ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 O))
  have hlog : Real.log (O+1:ℝ) ≤ 2*Real.log s := by
    have he := Real.log_le_log (by positivity : (0:ℝ)<O+1) hO
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hs.ne'] at he
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hfloor : (⌊2*(k:ℝ)/(m*η)⌋₊:ℝ) ≤ (k:ℝ)/4000000000 := by
    refine (Nat.floor_le (by positivity)).trans ?_
    apply (div_le_iff₀ hm0).mpr
    have hh := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ k by positivity)
    nlinarith only [hh]
  rw [←Real.exp_log (by positivity : (0:ℝ)<O+1),←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  calc
    _  ≤  ((k:ℝ)/4000000000)*(2*Real.log s) :=
      mul_le_mul hfloor hlog hlog0 (by positivity)
    _ = _ := by ring

end BinaryCoordinateSweeps.Sparse

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

lemma grid_log_upper {b r : ℕ} {bits : Fin b → ℕ} (hd : ∀j, bits j ≤ 2*r) :
    Real.log (gridSize bits) ≤ (b:ℝ)*(2*(r:ℝ)*Real.log 2) := by
  calc
    _ = ∑j : Fin b, (bits j:ℝ)*Real.log 2 := by
      rw [log_gridSize]
      simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    _  ≤  ∑_j : Fin b, 2*(r:ℝ)*Real.log 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd j) (Real.log_nonneg (by norm_num))
    _ = _ := by simp

lemma few_axis_eta_large {b r : ℕ} {bits : Fin b → ℕ}
    (hb : b ≤ 16000) (hd : ∀j, r ≤ bits j ∧ bits j ≤ 2*r)
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits)) (j : Fin b) :
    (8000000000:ℝ) ≤ (2^bits j:ℕ)*Real.exp (-Real.log (gridSize bits)/160000) := by
  have hbR : (b:ℝ) ≤ 16000 := by exact_mod_cast hb
  have hr : 0 ≤ (r:ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hu := grid_log_upper (fun j => (hd j).2)
  have hux := mul_le_mul_of_nonneg_right hbR hr
  have hj := mul_le_mul_of_nonneg_right (show (r:ℝ) ≤ bits j by exact_mod_cast (hd j).1)
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  calc
    _  ≤  Real.log (gridSize bits)/40000+1 := by linarith
    _  ≤  Real.exp (Real.log (gridSize bits)/40000) := Real.add_one_le_exp _
    _  ≤  _ := by
      rw [←Real.exp_log (by positivity : (0:ℝ)<((2^bits j:ℕ):ℝ)),←Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
      linarith

lemma outside_card_add_one_le {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :
    (Fintype.card (GridOutside bits j)+1:ℝ) ≤ 2*(gridSize bits:ℝ) := by
  have he := outside_card_mul_axis bits j
  have hp : 1 ≤ 2^bits j := Nat.one_le_pow _ _ (by omega)
  have hle : Fintype.card (GridOutside bits j) ≤ gridSize bits := by nlinarith
  have hg : 1 ≤ gridSize bits := gridSize_pos bits
  exact_mod_cast (show Fintype.card (GridOutside bits j)+1 ≤ 2*gridSize bits from by omega)

lemma few_cutoff_bounds (b k : ℕ) (hb : 1 ≤ b) (hbB : b ≤ 16000) :
    2*((k/4+1)-1+2*b*((k/(8*b)+1)-1)) ≤ k ∧
    (k:ℝ) ≤ 8*(((k/4+1+1)/2:ℕ):ℝ) ∧
    (k:ℝ) ≤ 128000*(k/(8*b)+1:ℕ) := by
  have h1 := Nat.div_mul_le_self k 4
  have h2 := Nat.div_mul_le_self k (8*b)
  have hmod := Nat.mod_lt k (by omega : 0<8*b)
  have he := Nat.mod_add_div k (8*b)
  constructor
  · simp only [Nat.add_sub_cancel]
    nlinarith
  constructor
  · exact_mod_cast (show k ≤ 8*((k/4+1+1)/2) from by omega)
  · have ht : k ≤ (8*b)*(k/(8*b)+1) := by nlinarith
    have hh := ht.trans (Nat.mul_le_mul_right _ (show 8*b ≤ 128000 from by omega))
    exact_mod_cast hh

end BinaryCoordinateSweeps

end

end OAI
