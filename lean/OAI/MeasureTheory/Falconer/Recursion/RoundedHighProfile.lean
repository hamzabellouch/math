import OAI.MeasureTheory.Falconer.Recursion.ProfileHighMass
import OAI.MeasureTheory.Falconer.Geometry.RelativeGridError

namespace OAI

/-! High-slope length survives inward rounding, with the same explicit
endpoint loss as the total retained interval length. -/
namespace Falconer

theorem profileHighLength_eq_sum (f : ℝ → ℝ) (u : ℝ) (S : List (ℝ × ℝ)) :
    profileHighLength f u S =
      (S.map fun c => if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0).sum := by
  induction S with
  | nil => simp [profileHighLength]
  | cons c S ih =>
    by_cases hc : u ≤ intervalSecantSlope f c.1 c.2 <;>
      simp [profileHighLength,hc,← ih]

theorem rounded_profile_high_length_lower {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (hmesh : 2/(n:ℝ) ≤ τ/2)
    (S : List (ℝ × ℝ)) (hmin : ∀ c ∈ S, τ ≤ c.2) (u : ℝ) :
    profileHighLength f u S-(2/(n:ℝ))*(S.length:ℝ) ≤
      profileHighLength f (u-16/((n:ℝ)*τ)) (S.map (innerProfileCell n)) := by
  have hpoint (c : ℝ × ℝ) (hc : c ∈ S) :
      (if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0)-2/(n:ℝ) ≤
        if u-16/((n:ℝ)*τ) ≤ intervalSecantSlope f (innerProfileCell n c).1 (innerProfileCell n c).2
          then (innerProfileCell n c).2 else 0 := by
    have hslope := (abs_le.mp (rounded_profile_uniform_slope hf hn hτ hmesh c (hmin c hc))).1
    have hlength := (innerProfileCell_length_bounds hn c).1
    have hpos : 0 < (innerProfileCell n c).2 := by
      have hh := hmin c hc
      linarith
    by_cases hu : u ≤ intervalSecantSlope f c.1 c.2
    · have hu' : u-16/((n:ℝ)*τ) ≤
          intervalSecantSlope f (innerProfileCell n c).1 (innerProfileCell n c).2 := by linarith
      simpa only [ite_eq_left hu,ite_eq_left hu'] using hlength
    · rw [ite_eq_right hu]
      split_ifs <;> have hnonneg : (0:ℝ) ≤ 2/(n:ℝ) := by positivity
      all_goals linarith
  rw [profileHighLength_eq_sum,profileHighLength_eq_sum,List.map_map]
  induction S with
  | nil => simp
  | cons c S ih =>
    have hh := hpoint c (by simp)
    have ht := ih (fun d hd => hmin d (by simp [hd])) (fun d hd => hpoint d (by simp [hd]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Function.comp_apply]
    linarith

end Falconer

end OAI
