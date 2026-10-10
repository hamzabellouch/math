import OAI.MeasureTheory.Falconer.Recursion.RoundedHighProfile
import OAI.MeasureTheory.Falconer.Recursion.OrderedProfilePower

namespace OAI

/-! Add normal and good interval gains while charging the actual chord-error
length and one fixed weak loss per interval. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def profileGainExponent (f : ℝ → ℝ) (u s η a loss N : ℝ)
    (c : ℝ × ℝ) : ℝ :=
  N*((s-a)*c.2+η*(if u ≤ intervalSecantSlope f c.1 c.2 then c.2 else 0)-loss)

theorem profile_gain_exponent_sum (S : List (ℝ × ℝ)) (f : ℝ → ℝ) (u s η a loss N : ℝ) :
    (S.map (profileGainExponent f u s η a loss N)).sum =
      N*((s-a)*(S.map Prod.snd).sum+η*profileHighLength f u S-loss*(S.length:ℝ)) := by
  rw [profileHighLength_eq_sum]
  induction S with
  | nil => simp
  | cons c S ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [ih]
    dsimp [profileGainExponent]
    ring

theorem profile_gain_exponent_lower (S : List (ℝ × ℝ)) (f : ℝ → ℝ)
    {u s η a loss N κ h J target : ℝ} (hN : 0 ≤ N) (hs : 0 ≤ s)
    (hη : 0 ≤ η) (ha : 0 ≤ a) (hloss : 0 ≤ loss)
    (hcover : 1-κ ≤ (S.map Prod.snd).sum) (hlength : (S.map Prod.snd).sum ≤ 1)
    (hhigh : h ≤ profileHighLength f u S) (hcount : (S.length:ℝ) ≤ J)
    (hgap : target ≤ s*(1-κ)+η*h-a-loss*J) :
    target*N ≤ (S.map (profileGainExponent f u s η a loss N)).sum := by
  rw [profile_gain_exponent_sum]
  have hbase := mul_le_mul_of_nonneg_left hcover hs
  have herror := mul_le_mul_of_nonneg_left hlength ha
  have hbonus := mul_le_mul_of_nonneg_left hhigh hη
  have htotal := mul_le_mul_of_nonneg_left hcount hloss
  have hsum : target ≤ (s-a)*(S.map Prod.snd).sum+
      η*profileHighLength f u S-loss*(S.length:ℝ) := by
    nlinarith only [hgap,hbase,herror,hbonus,htotal]
  simpa only [mul_comm N] using mul_le_mul_of_nonneg_right hsum hN

end Falconer

end OAI
