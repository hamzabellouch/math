import Mathlib
import OAI.Combinatorics.UniformKServer.ActualLevelPilot
import OAI.Combinatorics.UniformKServer.LevelTierLedger
import OAI.Combinatorics.UniformKServer.LevelKeyLedger

namespace OAI

noncomputable section

/-! Actual stationary posterior errors are charged to the insertion masses.
The designated mover is not incorrectly treated as post-request mass. -/
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance indexDecEqMass : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqMass : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

theorem heavy_bridge (I : Input X N) (n : Fin N) :
    I.data.heavy n↔TierPilot.heavy I.P I.r (I.μ n) (I.center n) := by
  simp only [data,TierPilot.heavy,mass_bridge]

theorem error_mass_bound (I : Input X N) (n : Fin N) (s : X→ℝ)
    (hs : ∀ p, 0≤ s p) (hsμ : ∀ p, s p≤I.μ n p) :
    (∑ p, s p*I.data.errorIndicator I.P.gammaH n p)≤
      TierPilot.insertionMass I.P I.r (I.μ n) (I.center n) := by
  by_cases hh : I.data.heavy n
  · rw [TierPilot.insertionMass,ite_eq_left ((I.heavy_bridge n).mp hh),
      TierPilot.annulus_identity I.r I.P.gammaH 51200 I.r_pos.le (by linarith [I.P.gammaH_small])]
    apply sum_le_sum
    intro p _
    change s p*(if dist (I.center n) p≤22*I.r ∧ (¬I.data.heavy n ∨ I.P.gammaH*I.r<dist (I.center n) p) then 1 else 0)≤_
    by_cases h : dist (I.center n) p≤22*I.r ∧ I.P.gammaH*I.r<dist (I.center n) p
    · have hp : dist (I.center n) p≤51200*I.r := by nlinarith [I.r_pos]
      simp only [hh,not_true_eq_false,false_or,ite_eq_left h,ite_eq_left (show I.P.gammaH*I.r<dist (I.center n) p ∧ dist (I.center n) p≤51200*I.r from ⟨h.2,hp⟩),mul_one]
      exact hsμ p
    · simp only [hh,not_true_eq_false,false_or,ite_eq_right h,mul_zero]
      split_ifs <;> [exact (hs p).trans (hsμ p); exact le_rfl]
  · rw [TierPilot.insertionMass,ite_eq_right (fun h=>hh ((I.heavy_bridge n).mpr h))]
    apply sum_le_sum
    intro p _
    change s p*(if dist (I.center n) p≤22*I.r ∧ (¬I.data.heavy n ∨ I.P.gammaH*I.r<dist (I.center n) p) then 1 else 0)≤_
    by_cases h : dist (I.center n) p≤22*I.r
    · have hp : dist (I.center n) p≤20480000*I.r := by nlinarith [I.r_pos]
      simp only [hh,not_false_eq_true,true_or,and_true,ite_eq_left h,mul_one,ite_eq_left hp]
      exact hsμ p
    · simp only [hh,not_false_eq_true,true_or,and_true,ite_eq_right h,mul_zero]
      split_ifs <;> [exact (hs p).trans (hsμ p); exact le_rfl]

theorem stationary_tier_charge (I : Input X N) (n : Fin N) (i : Fin I.height)
    (s : X→ℝ) (hs : ∀ p, 0≤ s p) (hsμ : ∀ p, s p≤I.μ n p) :
    (∑ p, s p*I.data.stationaryBudget I.P.gammaH n i p)≤98*I.shortCharge i n.val := by
  unfold LevelMap.Data.stationaryBudget shortCharge
  rw [dite_eq_left n.isLt]
  change (∑ p, s p*(if I.data.tierTrigger n i then _ else _))≤98*(if I.data.tierTrigger n i then _ else _)
  by_cases ht : I.data.tierTrigger n i
  · simp only [ite_eq_left ht]
    change (∑ p, s p*(98*I.r/(I.data.K i:ℝ)*I.data.errorIndicator I.P.gammaH n p))≤98*(I.r*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n)/(I.data.K i:ℝ))
    have he : (∑ p, s p*(98*I.r/(I.data.K i:ℝ)*I.data.errorIndicator I.P.gammaH n p))=
        (98*I.r/(I.data.K i:ℝ))*(∑ p, s p*I.data.errorIndicator I.P.gammaH n p) := by
      rw [mul_sum]; apply sum_congr rfl; intro p _; ring
    rw [he]
    have h := mul_le_mul_of_nonneg_left (I.error_mass_bound n s hs hsμ)
      (show 0≤98*I.r/(I.data.K i:ℝ) from div_nonneg (mul_nonneg (by norm_num) I.r_pos.le) (Nat.cast_nonneg _))
    exact h.trans_eq (by ring)
  · simp only [ite_eq_right ht,mul_zero,sum_const_zero,le_refl]

theorem stationary_heavy_charge (I : Input X N) (n : Fin N)
    (s : X→ℝ) (hs : ∀ p, 0≤ s p) (hsμ : ∀ p, s p≤I.μ n p) :
    (∑ p, s p*I.data.heavyStationaryBudget n p)≤I.longCharge n.val := by
  unfold LevelMap.Data.heavyStationaryBudget longCharge
  rw [dite_eq_left n.isLt]
  change (∑ p, s p*(if I.data.heavyTrigger n ∧ 3*I.r<dist (I.center n) p ∧ dist (I.center n) p≤120*I.r then 2*I.r else 0))≤
    (if I.data.heavyTrigger n then 127*I.r*HeavyPilot.annulusMass I.r (I.μ n) (I.center n) else 0)
  by_cases ht : I.data.heavyTrigger n
  · simp only [ht,true_and,ite_true,HeavyPilot.annulusMass,mul_sum]
    apply sum_le_sum
    intro p _
    rw [dist_comm p]
    split_ifs with hp
    · have hm := mul_le_mul_of_nonneg_left (hsμ p) I.r_pos.le
      have hn := mul_nonneg I.r_pos.le ((hs p).trans (hsμ p))
      nlinarith
    · simp only [mul_zero,le_refl]
  · simp only [ht,false_and,ite_false,mul_zero,sum_const_zero,le_refl]

end UniformKServer.PartitionLevel.Input

end

end OAI
