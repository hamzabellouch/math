import OAI.MeasureTheory.Falconer.Estimates.DyadicTree
import Mathlib.Tactic.Positivity

namespace OAI

/-! # A dyadic block schedule with two initial blocks reserved for freezing -/

namespace Falconer

def radialBlockSize (N J : ℕ) : ℕ := N/(J+2)

def radialBlockDepth (N J j : ℕ) : ℕ :=
  N-J*radialBlockSize N J+j*radialBlockSize N J

theorem radialBlockSize_total (N J : ℕ) : (J+2)*radialBlockSize N J ≤ N :=
  Nat.mul_div_le N (J+2)

theorem radialBlockDepth_le (N J : ℕ) {j : ℕ} (hj : j ≤ J) :
    radialBlockDepth N J j ≤ N := by
  have hh := radialBlockSize_total N J
  have hm := Nat.mul_le_mul_right (radialBlockSize N J) hj
  have hJB : J*radialBlockSize N J ≤ N := by nlinarith
  have he := Nat.sub_add_cancel hJB
  unfold radialBlockDepth
  omega

theorem radialBlockDepth_final (N J : ℕ) : radialBlockDepth N J J = N := by
  have hh := radialBlockSize_total N J
  unfold radialBlockDepth
  have hle : J*radialBlockSize N J ≤ N := by nlinarith
  exact Nat.sub_add_cancel hle

theorem radialBlockDepth_step (N J j : ℕ) :
    radialBlockDepth N J (j+1) = radialBlockDepth N J j+radialBlockSize N J := by
  unfold radialBlockDepth
  ring

theorem radialBlockDepth_mono (N J : ℕ) : Monotone (radialBlockDepth N J) := by
  intro i j hij
  unfold radialBlockDepth
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem radialBlockDepth_two_blocks (N J j : ℕ) :
    2*radialBlockSize N J ≤ radialBlockDepth N J j := by
  have hh := radialBlockSize_total N J
  have hJB : J*radialBlockSize N J ≤ N := by nlinarith
  have he := Nat.sub_add_cancel hJB
  unfold radialBlockDepth
  nlinarith

theorem radialBlockDepth_initial_upper {N : ℕ} (hN : 0 < N) (J : ℕ) :
    (radialBlockDepth N J 0:ℝ)/(N:ℝ) ≤ 2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hJ : (0:ℝ) < (J:ℝ)+2 := by positivity
  have ht := Nat.lt_mul_div_succ N (by omega : 0 < J+2)
  have ht' : (N:ℝ) < ((J:ℝ)+2)*((radialBlockSize N J:ℝ)+1) := by
    exact_mod_cast ht
  have htotal := radialBlockSize_total N J
  have hjb : J*radialBlockSize N J ≤ N := by nlinarith
  have he : (radialBlockDepth N J 0:ℝ) = (N:ℝ)-(J:ℝ)*(radialBlockSize N J:ℝ) := by
    simp only [radialBlockDepth,zero_mul,Nat.add_zero,Nat.cast_sub hjb,Nat.cast_mul]
  rw [he]
  apply (div_le_iff₀ hN').mpr
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) J]

end Falconer

end OAI
