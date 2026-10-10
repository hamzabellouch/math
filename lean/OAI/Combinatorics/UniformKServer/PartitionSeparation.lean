import Mathlib
import OAI.Combinatorics.UniformKServer.LevelSeparation
import OAI.Combinatorics.UniformKServer.LevelHeavy
import OAI.Combinatorics.UniformKServer.PartitionLevel

namespace OAI

                                          
section

/-! The actual one-level final-map separation estimate with its local mass
ratio, and the exact zero contribution at large heavy levels. -/
noncomputable section
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance sepFinDecEq (m : ℕ) : DecidableEq (Fin m) := fun a b => Classical.propDecidable (a=b)
local instance sepPairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def separation (I : Input X N) (n : Fin N) (p : X) : ℝ :=
  I.data.law.expect (fun ω => indicator (I.data.key I.order ω (n.val+1) (I.center n))
    (I.data.key I.order ω (n.val+1) p))

theorem separation_nonneg (I : Input X N) (n : Fin N) (p : X) : 0 ≤ I.separation n p := by
  apply Law.expect_nonneg
  intro ω
  unfold indicator
  split_ifs <;> norm_num

theorem separation_le_one (I : Input X N) (n : Fin N) (p : X) : I.separation n p ≤ 1 := by
  have h := I.data.law.expect_mono (fun ω => indicator (I.data.key I.order ω (n.val+1) (I.center n))
    (I.data.key I.order ω (n.val+1) p)) (fun _ => 1) (fun ω => by
    show indicator _ _ ≤ (1:ℝ)
    unfold indicator
    split_ifs <;> norm_num)
  simpa only [separation,Law.expect_const] using h

theorem log_prefix (I : Input X N) (n : Fin N) :
    ((I.order.take (I.cutoff n)).map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2))).sum ≤
      (16*I.C+32)*max 1 (I.localLog n) := by
  have hb (is : List (Fin I.height)) :
      (is.map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2))).sum ≤
        (4*I.C+8)*(is.map (fun i => DyadicTiers.value i.val)).sum := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons,List.sum_cons,mul_add]
      apply add_le_add _ ih
      have h := TierParameters.radius_parameter I.C (DyadicTiers.value i.val)
        I.C_one (DyadicTiers.one_le_value i.val)
      change 2*Real.log (1+(TierParameters.cutoff I.C (DyadicTiers.value i.val):ℝ)^2) ≤ _
      nlinarith only [h]
  have hp := mul_le_mul_of_nonneg_left (I.prefix_sum n) (by linarith [I.C_one] : 0 ≤ 4*I.C+8)
  exact (hb _).trans (by nlinarith only [hp])

theorem short_separation (I : Input X N) (n : Fin N) (p : X)
    (hp : dist (I.center n) p<I.r/4) :
    I.r*I.separation n p ≤ (16*I.C+33)*(1+I.localLog n)*dist (I.center n) p := by
  have h := LevelMap.Data.prefix_separation I.data (I.order.take (I.cutoff n))
    (I.order.drop (I.cutoff n)) n (I.prefix_exists n) p hp
  rw [List.take_append_drop] at h
  have he (is : List (Fin I.height)) :
      (is.map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2)*dist (I.center n) p/I.r)).sum=
        (is.map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2))).sum*(dist (I.center n) p/I.r) := by
    induction is with
    | nil => simp
    | cons i is ih => simp only [List.map_cons,List.sum_cons,ih]; ring
  change I.separation n p ≤ dist (I.center n) p/I.r+
    ((I.order.take (I.cutoff n)).map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2)*dist (I.center n) p/I.r)).sum at h
  rw [he] at h
  have hratio : 0 ≤ dist (I.center n) p/I.r := div_nonneg dist_nonneg I.r_pos.le
  have hb := mul_le_mul_of_nonneg_right (I.log_prefix n) hratio
  have hmax : max 1 (I.localLog n) ≤ 1+I.localLog n := by
    exact max_le (by linarith [I.localLog_nonneg n]) (by linarith)
  have hc : 0 ≤ 16*I.C+32 := by linarith [I.C_one]
  have hg := mul_le_mul_of_nonneg_left hmax hc
  have hcoef : 1+(16*I.C+32)*max 1 (I.localLog n) ≤ (16*I.C+33)*(1+I.localLog n) := by
    nlinarith only [hg,I.localLog_nonneg n]
  have hprod := mul_le_mul_of_nonneg_right hcoef hratio
  have hbound : I.separation n p ≤ ((16*I.C+33)*(1+I.localLog n)*dist (I.center n) p)/I.r := by
    change I.separation n p ≤ _ at h
    calc
      _ ≤ dist (I.center n) p/I.r+
        ((I.order.take (I.cutoff n)).map (fun i => 2*Real.log (1+(I.data.K i:ℝ)^2))).sum*
        (dist (I.center n) p/I.r) := h
      _ ≤ dist (I.center n) p/I.r+(16*I.C+32)*max 1 (I.localLog n)*(dist (I.center n) p/I.r) := by linarith only [hb]
      _ = (1+(16*I.C+32)*max 1 (I.localLog n))*(dist (I.center n) p/I.r) := by ring
      _ ≤ (16*I.C+33)*(1+I.localLog n)*(dist (I.center n) p/I.r) := hprod
      _ = _ := by ring
  have hfinal := (le_div_iff₀ I.r_pos).mp hbound
  nlinarith only [hfinal]

theorem heavy_zero (I : Input X N) (n : Fin N) (p : X) (hh : I.data.heavy n)
    (hp : dist (I.center n) p ≤ 8*I.r) : I.separation n p=0 := by
  unfold separation
  have he (ω : LevelMap.Tape I.data) := LevelMap.Data.heavy_same_key I.data I.order n hh ω p hp
  change ∀ ω, I.data.key I.order ω (n.val+1) (I.center n)=I.data.key I.order ω (n.val+1) p at he
  simp only [he,indicator,ite_true,Law.expect_const]

end UniformKServer.PartitionLevel.Input

end


end

end OAI
