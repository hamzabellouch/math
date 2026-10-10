import Mathlib
import OAI.Combinatorics.UniformKServer.LevelMassLedger
import OAI.Combinatorics.UniformKServer.LevelMoverBudget

namespace OAI

noncomputable section

/-! Actual insertion charges and local logarithmic motion pay the level ledger. -/
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance ixAllow : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairAllow : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def charges (I : Input X N) (n : Fin N) : ℝ :=
  I.longCharge n.val+(I.order.map fun i=>I.shortCharge i n.val).sum

def nonheavyMotion (I : Input X N) (n : Fin N) (p : X) : ℝ :=
  if I.data.heavy n then 0 else dist (I.center n) p

theorem charges_nonneg (I : Input X N) (n : Fin N) : 0≤I.charges n := by
  exact add_nonneg (I.long_charge_nonneg n.val) (List.sum_nonneg (fun a ha=>by obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha; exact I.short_charge_nonneg i n.val))

theorem heavy_mover_bound (I : Input X N) (n : Fin N) (p : X) :
    I.data.heavyMoverBudget n p≤I.smallError n p+I.nonheavyMotion n p := by
  unfold LevelMap.Data.heavyMoverBudget nonheavyMotion
  apply add_le_add _ (le_refl (if I.data.heavy n then (0:ℝ) else dist (I.center n) p))
  change (if I.data.heavyTrigger n ∧ 3*I.r<dist (I.center n) p then I.r else 0)≤_
  split_ifs with ht
  · have gamma_bound : I.P.gammaH ≤ 3 := I.P.gammaH_small.trans (by norm_num)
    have hp : I.P.gammaH*I.r<dist (I.center n) p :=
      (mul_le_mul_of_nonneg_right gamma_bound I.r_pos.le).trans_lt ht.2
    rw [smallError,ite_eq_left hp]
  · exact I.smallError_nonneg n p

theorem stationary_allowance (I : Input X N) (n : Fin N) (s : X→ℝ)
    (hs : ∀ p, 0≤ s p) (hsμ : ∀ p, s p≤I.μ n p) :
    (∑ p,s p*I.data.stationaryAllowance I.order I.P.gammaH n p)≤98*I.charges n := by
  have ht (is : List (Fin I.height)) :
      (∑ p,s p*(is.map fun i=>I.data.stationaryBudget I.P.gammaH n i p).sum)≤
        98*(is.map fun i=>I.shortCharge i n.val).sum := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons,List.sum_cons,mul_add,sum_add_distrib]
      exact add_le_add (I.stationary_tier_charge n i s hs hsμ) ih
  unfold LevelMap.Data.stationaryAllowance charges
  simp only [mul_add,sum_add_distrib]
  have hh := I.stationary_heavy_charge n s hs hsμ
  have hn := I.long_charge_nonneg n.val
  have h := ht I.order
  linarith

theorem mover_allowance (I : Input X N) (n : Fin N) (p : X) :
    I.data.moverAllowance I.order I.P.gammaH n p≤49*I.charges n+
      99*I.smallError n p+I.nonheavyMotion n p+(8*I.C+24)*I.localLog n*dist (I.center n) p := by
  have hh := I.heavy_mover_bound n p
  have ht := I.mover_tiers n p
  have hn := I.long_charge_nonneg n.val
  unfold LevelMap.Data.moverAllowance charges
  linarith

end UniformKServer.PartitionLevel.Input

end

end OAI
