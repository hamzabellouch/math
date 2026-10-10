import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingHomeomorph

namespace OAI

/-! Compact cutoffs of bounded Lipschitz directions, normalized to
preserve the exact Lipschitz constant one. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def directionTent (R y : ℝ) : ℝ := max (1-|y|/R) 0

theorem directionTent_nonneg (R y : ℝ) : 0≤directionTent R y := le_max_right _ _

theorem directionTent_le_one (R : ℝ) (hR : 0<R) (y : ℝ) : directionTent R y≤1 := by
  apply max_le
  · have := div_nonneg (abs_nonneg y) hR.le
    linarith
  · norm_num

theorem directionTent_zero (R : ℝ) (hR : 0<R) (y : ℝ) (hy : R≤|y|) :
    directionTent R y=0 := by
  apply max_eq_right
  have hh : 1≤|y|/R := (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hy)
  linarith

theorem directionTent_difference (R : ℝ) (hR : 0<R) (x y : ℝ) :
    |directionTent R x-directionTent R y|≤|x-y|/R := by
  have hh := abs_max_sub_max_le_abs (1-|x|/R) (1-|y|/R) 0
  calc
    _ ≤ |(1-|x|/R)-(1-|y|/R)| := hh
    _ = |(|x|-|y|)|/R := by
      rw [show (1-|x|/R)-(1-|y|/R)=-( (|x|-|y|)/R) by ring,abs_neg,abs_div,abs_of_pos hR]
    _ ≤ |x-y|/R := div_le_div_of_nonneg_right (abs_abs_sub_abs_le x y) hR.le

def compactDirectionCutoff (u : ℝ → ℝ) (R : ℝ) (y : ℝ) : ℝ :=
  (R/(R+1))*u y*directionTent R y

theorem compactDirectionCutoff_compact (u : ℝ → ℝ) (R : ℝ) (hR : 0<R) :
    HasCompactSupport (compactDirectionCutoff u R) := by
  apply HasCompactSupport.intro (isCompact_Icc (a:= -R) (b:=R))
  intro y hy
  have habs : R < |y| := lt_of_not_ge (fun hh => hy (abs_le.mp hh))
  simp only [compactDirectionCutoff,directionTent_zero R hR y habs.le,mul_zero]

theorem compactDirectionCutoff_bound (u : ℝ → ℝ) (hb : ∀ x, |u x|≤1)
    (R : ℝ) (hR : 0<R) (y : ℝ) : |compactDirectionCutoff u R y|≤1 := by
  have ha : 0≤R/(R+1) := by positivity
  have ha' : R/(R+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  rw [compactDirectionCutoff,abs_mul,abs_mul,abs_of_nonneg ha,
    abs_of_nonneg (directionTent_nonneg R y)]
  calc
    _ ≤ 1*1*1 := mul_le_mul (mul_le_mul ha' (hb y) (abs_nonneg _) (by norm_num))
      (directionTent_le_one R hR y) (directionTent_nonneg R y) (by norm_num)
    _ = 1 := by norm_num

theorem compactDirectionCutoff_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hb : ∀ x, |u x|≤1) (R : ℝ) (hR : 0<R) :
    LipschitzWith 1 (compactDirectionCutoff u R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |compactDirectionCutoff u R x-compactDirectionCutoff u R y|≤1*|x-y|
  have ha : 0≤R/(R+1) := by positivity
  have hu' : |u x-u y|≤|x-y| := by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hu.dist_le_mul x y
  have he : compactDirectionCutoff u R x-compactDirectionCutoff u R y=
      (R/(R+1))*(u x*(directionTent R x-directionTent R y)+(u x-u y)*directionTent R y) := by
    simp only [compactDirectionCutoff]
    ring
  rw [he,abs_mul,abs_of_nonneg ha]
  calc
    _ ≤ (R/(R+1))*(|u x*(directionTent R x-directionTent R y)|+|(u x-u y)*directionTent R y|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) ha
    _ = (R/(R+1))*(|u x| *|directionTent R x-directionTent R y|+
        |u x-u y| *directionTent R y) := by rw [abs_mul,abs_mul,abs_of_nonneg (directionTent_nonneg R y)]
    _ ≤ (R/(R+1))*(1*(|x-y|/R)+|x-y| *1) := by
      apply mul_le_mul_of_nonneg_left _ ha
      exact add_le_add
        (mul_le_mul (hb x) (directionTent_difference R hR x y) (abs_nonneg _) (by norm_num))
        (mul_le_mul hu' (directionTent_le_one R hR y) (directionTent_nonneg R y) (abs_nonneg _))
    _ = 1*|x-y| := by field_simp [hR.ne',ne_of_gt (show 0<R+1 by linarith)]; ring

theorem compactDirectionCutoff_tendsto (u : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n : ℕ => compactDirectionCutoff u ((n:ℝ)+1) x) atTop (𝓝 (u x)) := by
  have ha : Tendsto (fun n : ℕ => ((n:ℝ)+1)/((n:ℝ)+1+1)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_div_add_atTop (1:ℝ)).comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun n : ℕ => |x|/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,mul_one,div_eq_mul_inv,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul |x|
  have ht : Tendsto (fun n : ℕ => directionTent ((n:ℝ)+1) x) atTop (𝓝 (1:ℝ)) := by
    have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h0 : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    simpa only [directionTent,sub_zero,max_eq_left (by norm_num : (0:ℝ)≤1)] using
      (h1.sub hb).max h0
  simpa only [compactDirectionCutoff,one_mul,mul_one] using (ha.mul_const (u x)).mul ht

end LipschitzHilbert.PacketRepresentation

end

end OAI
