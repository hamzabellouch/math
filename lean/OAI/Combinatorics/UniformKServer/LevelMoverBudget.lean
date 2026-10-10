import Mathlib
import OAI.Combinatorics.UniformKServer.ActualLevelPilot
import OAI.Combinatorics.UniformKServer.LevelTierLedger
import OAI.Combinatorics.UniformKServer.LevelErrorMass

namespace OAI

noncomputable section

/-! Designated-mover error: nonheavy insertions are financed by positive
post-request mass; heavy insertions are a geometric small-scale error. -/
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance indexDecEqMover : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqMover : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def smallError (I : Input X N) (n : Fin N) (p : X) : ℝ :=
  if I.P.gammaH*I.r<dist (I.center n) p then I.r else 0

def unqualifiedMotion (I : Input X N) (n : Fin N) (i : Fin I.height) (p : X) : ℝ :=
  if I.data.qualify i n then 0 else (4+2*Real.log (1+(I.data.K i:ℝ)^2))*dist (I.center n) p

theorem smallError_nonneg (I : Input X N) (n : Fin N) (p : X) : 0≤I.smallError n p := by
  unfold smallError; split_ifs <;> [exact I.r_pos.le; exact le_rfl]

theorem unqualified_nonneg (I : Input X N) (n : Fin N) (i : Fin I.height) (p : X) :
    0≤I.unqualifiedMotion n i p := by
  unfold unqualifiedMotion
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by linarith [Real.log_nonneg (show (1:ℝ)≤1+(I.data.K i:ℝ)^2 by linarith [sq_nonneg (I.data.K i:ℝ)])]) dist_nonneg

theorem insertion_mass_one (I : Input X N) (n : Fin N) (hh : ¬I.data.heavy n) :
    1≤TierPilot.insertionMass I.P I.r (I.μ n) (I.center n) := by
  rw [TierPilot.insertionMass,ite_eq_right (fun h=>hh ((I.heavy_bridge n).mpr h)),mass_bridge]
  exact (I.served n).trans (GeometricMass.mass_center _ (I.μ_nonneg n) _ _ (mul_nonneg (by norm_num) I.r_pos.le))

theorem shortCharge_at (I : Input X N) (n : Fin N) (i : Fin I.height) :
    I.shortCharge i n.val=if I.data.tierTrigger n i then
      I.r*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n)/(I.data.K i:ℝ) else 0 := by
  unfold shortCharge
  rw [dite_eq_left n.isLt]
  rfl

theorem mover_budget_bound (I : Input X N) (n : Fin N) (i : Fin I.height) (p : X) :
    I.data.moverBudget I.P.gammaH n i p≤49*I.shortCharge i n.val+
      (49/(I.data.K i:ℝ))*I.smallError n p+I.unqualifiedMotion n i p := by
  have hr := I.r_pos
  have hK : (0:ℝ)<I.data.K i := by exact_mod_cast (show 0<I.data.K i by have := I.data.two i; omega)
  have hsmall := mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤49) hK.le) (I.smallError_nonneg n p)
  have hu := I.unqualified_nonneg n i p
  rw [shortCharge_at]
  unfold LevelMap.Data.moverBudget
  by_cases ht : I.data.tierTrigger n i
  · simp only [ite_eq_left ht]
    change 49*I.r/(I.data.K i:ℝ)*I.data.errorIndicator I.P.gammaH n p≤_
    by_cases hh : I.data.heavy n
    · have herr : 49*I.r/(I.data.K i:ℝ)*I.data.errorIndicator I.P.gammaH n p≤
          (49/(I.data.K i:ℝ))*I.smallError n p := by
        unfold LevelMap.Data.errorIndicator smallError
        change 49*I.r/(I.data.K i:ℝ)*(if dist (I.center n) p≤22*I.r ∧ (¬I.data.heavy n ∨ I.P.gammaH*I.r<dist (I.center n) p) then 1 else 0)≤_
        simp only [hh,not_true_eq_false,false_or]
        by_cases hp : I.P.gammaH*I.r<dist (I.center n) p
        · rw [ite_eq_left hp]
          by_cases hn : dist (I.center n) p≤22*I.r
          · rw [ite_eq_left ⟨hn,hp⟩,mul_one]
            exact le_of_eq (by ring)
          · rw [ite_eq_right (fun h=>hn h.1),mul_zero]
            exact mul_nonneg (div_nonneg (by norm_num) hK.le) hr.le
        · have hnot : ¬(dist (I.center n) p≤22*I.r ∧ I.P.gammaH*I.r<dist (I.center n) p) := fun h=>hp h.2
          rw [ite_eq_right hnot,ite_eq_right hp,mul_zero,mul_zero]
      have hc := TierPilot.insertionMass_bounds I.P I.r I.r_pos.le (I.μ n) (I.μ_nonneg n) (I.center n)
      have hcn : 0≤49*(I.r*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n)/(I.data.K i:ℝ)) :=
        mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hr.le hc.1) hK.le)
      linarith
    · have he : I.data.errorIndicator I.P.gammaH n p≤1 := by
        unfold LevelMap.Data.errorIndicator; split_ifs <;> norm_num
      have hm := mul_le_mul_of_nonneg_left (I.insertion_mass_one n hh)
        (show 0≤49*I.r/(I.data.K i:ℝ) by positivity)
      have he' := mul_le_mul_of_nonneg_left he (show 0≤49*I.r/(I.data.K i:ℝ) by positivity)
      have heq : 49*(I.r*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n)/(I.data.K i:ℝ))=
          (49*I.r/(I.data.K i:ℝ))*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n) := by ring
      rw [heq]
      linarith
  · simp only [ite_eq_right ht,mul_zero,zero_add]
    change I.unqualifiedMotion n i p≤49/(I.data.K i:ℝ)*I.smallError n p+I.unqualifiedMotion n i p
    linarith

theorem unqualified_sum (I : Input X N) (n : Fin N) (p : X) :
    (I.order.map fun i=>I.unqualifiedMotion n i p).sum≤(8*I.C+24)*I.localLog n*dist (I.center n) p := by
  have hcoef : 0≤4*I.C+12 := by linarith [I.C_one]
  have hlocal := DyadicTiers.unqualified_sum (I.localLog n) (I.localLog_nonneg n) I.height
  have hp (i : Fin I.height) : I.unqualifiedMotion n i p≤
      (4*I.C+12)*dist (I.center n) p*(if DyadicTiers.value i.val<I.localLog n then DyadicTiers.value i.val else 0) := by
    unfold unqualifiedMotion
    by_cases hq : I.data.qualify i n
    · rw [ite_eq_left hq,ite_eq_right (not_lt.mpr ((I.qualification n i).mp hq)),mul_zero]
    · have hlt : DyadicTiers.value i.val<I.localLog n := lt_of_not_ge (fun h=>hq ((I.qualification n i).mpr h))
      rw [ite_eq_right hq,ite_eq_left hlt]
      have hlog := TierParameters.radius_parameter I.C (DyadicTiers.value i.val) I.C_one (DyadicTiers.one_le_value i.val)
      change Real.log (1+(I.data.K i:ℝ)^2)≤_ at hlog
      have h := mul_le_mul_of_nonneg_right (show 4+2*Real.log (1+(I.data.K i:ℝ)^2)≤(4*I.C+12)*DyadicTiers.value i.val by nlinarith [DyadicTiers.one_le_value i.val]) (dist_nonneg (x:=I.center n) (y:=p))
      nlinarith only [h]
  rw [order,List.map_ofFn,List.sum_ofFn]
  have hsum := sum_le_sum (fun i (_ : i∈(univ : Finset (Fin I.height)))=>hp i)
  rw [←mul_sum] at hsum
  have hconvert : (∑ i : Fin I.height,if DyadicTiers.value i.val<I.localLog n then DyadicTiers.value i.val else 0)=
      ∑ i∈range I.height,if DyadicTiers.value i<I.localLog n then DyadicTiers.value i else 0 := Fin.sum_univ_eq_sum_range (fun j=>if DyadicTiers.value j<I.localLog n then DyadicTiers.value j else 0) I.height
  rw [hconvert] at hsum
  have h := mul_le_mul_of_nonneg_left hlocal (mul_nonneg hcoef (dist_nonneg (x:=I.center n) (y:=p)))
  simp only [Function.comp_apply,id_eq]
  nlinarith only [hsum,h]

theorem mover_tiers (I : Input X N) (n : Fin N) (p : X) :
    (I.order.map fun i=>I.data.moverBudget I.P.gammaH n i p).sum≤
      49*(I.order.map fun i=>I.shortCharge i n.val).sum+98*I.smallError n p+
        (8*I.C+24)*I.localLog n*dist (I.center n) p := by
  have hsum : (I.order.map fun i=>I.data.moverBudget I.P.gammaH n i p).sum≤
      (I.order.map fun i=>49*I.shortCharge i n.val+(49/(I.data.K i:ℝ))*I.smallError n p+I.unqualifiedMotion n i p).sum :=
    List.sum_le_sum (fun i _=>I.mover_budget_bound n i p)
  have hi : (I.order.map fun i=>1/(I.data.K i:ℝ)).sum≤2 := by
    rw [order,List.map_ofFn,List.sum_ofFn]
    change (∑ i : Fin I.height,1/(TierParameters.cutoff I.C (DyadicTiers.value i.val):ℝ))≤2
    change (∑ i : Fin I.height,(fun j=>1/(TierParameters.cutoff I.C (DyadicTiers.value j):ℝ)) i.val)≤2
    rw [Fin.sum_univ_eq_sum_range (fun j=>1/(TierParameters.cutoff I.C (DyadicTiers.value j):ℝ)) I.height]
    exact DyadicTiers.inverse_sum I.C I.C_one I.height
  have hid := mul_le_mul_of_nonneg_right hi (mul_nonneg (by norm_num : (0:ℝ)≤49) (I.smallError_nonneg n p))
  have hu := I.unqualified_sum n p
  have he : (I.order.map fun i=>49*I.shortCharge i n.val+(49/(I.data.K i:ℝ))*I.smallError n p+I.unqualifiedMotion n i p).sum=
      49*(I.order.map fun i=>I.shortCharge i n.val).sum+
      (I.order.map fun i=>1/(I.data.K i:ℝ)).sum*(49*I.smallError n p)+(I.order.map fun i=>I.unqualifiedMotion n i p).sum := by
    simp only [order,List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq,mul_sum,sum_mul,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [he] at hsum
  linarith

end UniformKServer.PartitionLevel.Input

end

end OAI
