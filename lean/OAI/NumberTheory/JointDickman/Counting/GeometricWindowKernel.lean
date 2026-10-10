import OAI.NumberTheory.JointDickman.Probability.GeometricHistogramErrors
import OAI.NumberTheory.JointDickman.Amplification.LogMassBilinear

namespace OAI

/-! # The summed geometric windows form a uniformly bounded narrow kernel -/

namespace JointDickman
open Finset Filter

noncomputable def geometricWindowKernel (m B : ℕ) (t L U : ℝ) (S : Finset ℤ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (i j : Fin (channelFineCount m B)) : ℝ :=
  (B : ℝ)*∑ k ∈ S, if i ∈ geometricHistogramWindow m B t L U k ∧
    j ∈ geometricHistogramWindow m B t L U k then V k i j else 0

theorem geometricWindow_pair_distance {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U : ℝ} {k : ℤ} {i j : Fin (channelFineCount m B)}
    (hi : i ∈ geometricHistogramWindow m B t L U k)
    (hj : j ∈ geometricHistogramWindow m B t L U k) :
    |channelLower (channelFineCount m B) i-channelLower (channelFineCount m B) j| ≤
      (U-L+1)/B := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0))
  have hi' := (mem_filter.mp hi).2
  have hj' := (mem_filter.mp hj).2
  have hwi := channel_width (channelFineCount m B) i
  have hwj := channel_width (channelFineCount m B) j
  have hilo := (div_le_iff₀ hBr).mp hi'.2
  have hihi := (le_div_iff₀ hBr).mp hi'.1
  have hjlo := (div_le_iff₀ hBr).mp hj'.2
  have hjhi := (le_div_iff₀ hBr).mp hj'.1
  apply abs_le.mpr
  constructor
  · have hh : channelLower (channelFineCount m B) j-
        channelLower (channelFineCount m B) i ≤ (U-L+1)/B := by
      apply (le_div_iff₀ hBr).mpr
      nlinarith
    linarith
  · apply (le_div_iff₀ hBr).mpr
    nlinarith

theorem geometricWindowKernel_bounds {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U M : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hM : 0 ≤ M)
    (S : Finset ℤ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, |V k i j| ≤ M) :
    (∀ i j, |geometricWindowKernel m B t L U S V i j| ≤ (((1+U-L)/t+1)*M)*B) ∧
    (∀ i j, geometricWindowKernel m B t L U S V i j ≠ 0 →
      |channelLower (channelFineCount m B) i-channelLower (channelFineCount m B) j| ≤
        (U-L+1)/B) := by
  classical
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0))
  constructor
  · intro i j
    let A := S.filter (fun k => i ∈ geometricHistogramWindow m B t L U k)
    have hcard : (A.card : ℝ) ≤ (1+U-L)/t+1 :=
      (histogramWindow_overlap hBr ht hLU (channelFineCount_pos hm hBpos) S i).trans
        (by gcongr)
    have hterm (k : ℤ) (hk : k ∈ S) :
        |(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then V k i j else 0)| ≤
          if i ∈ geometricHistogramWindow m B t L U k then M else 0 := by
      by_cases hi : i ∈ geometricHistogramWindow m B t L U k
      · by_cases hj : j ∈ geometricHistogramWindow m B t L U k
        · simpa only [hi,hj,and_self,ite_true] using hV k hk i j
        · simpa [hi,hj] using hM
      · simp [hi]
    unfold geometricWindowKernel
    rw [abs_mul,abs_of_pos hBr]
    calc
      _ ≤ (B : ℝ)*∑ k ∈ S, |(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then V k i j else 0)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hBr.le
      _ ≤ (B : ℝ)*∑ k ∈ S, if i ∈ geometricHistogramWindow m B t L U k then M else 0 :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) hBr.le
      _ = (B : ℝ)*((A.card : ℝ)*M) := by rw [← sum_filter,sum_const,nsmul_eq_mul]
      _ ≤ (B : ℝ)*(((1+U-L)/t+1)*M) := by gcongr
      _ = _ := by ring
  · intro i j hne
    have hs : (∑ k ∈ S, if i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k then V k i j else 0) ≠ 0 := by
      intro hs
      exact hne (by simp [geometricWindowKernel,hs])
    obtain ⟨k,_hk,hkv⟩ := exists_ne_zero_of_sum_ne_zero hs
    have hij : i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k := by
      by_contra h
      exact hkv (ite_eq_right h)
    exact geometricWindow_pair_distance hm hB hij.1 hij.2

end JointDickman

end OAI
