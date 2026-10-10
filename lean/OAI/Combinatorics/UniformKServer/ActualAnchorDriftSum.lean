import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionMovement
import OAI.Combinatorics.UniformKServer.CurrentTesting
import OAI.Combinatorics.UniformKServer.ActualAnchorDrift

namespace OAI

                                           
section

/-! The individual retained-anchor hidden drift summed over exactly the
chosen mover and all stationary members. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def driftLog (k : ℕ) : ℝ := (6/5)*132*(2+7/Real.log 2)*Real.log (k+1)

theorem members_drift (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    (∑ a : Fin k,memberDrift A D hk z t ω a)≤
      (6/5)*132*A.q*coordinateCost A D hk z t ω+
      (driftLog k/3)*dist (D.position t ω (D.chosen t ω)) (D.request t ω) := by
  have hs := sum_le_sum (s:=univ) (fun a (_ : a∈(univ : Finset (Fin k)))=>member_drift A D hk z t ω a hdiam)
  have he : (∑ a : Fin k,∑ j : Fin J,GeometricMass.radius A.R A.q j.val*
       PrefixMovement.diff (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
         (word A D hk z t ω (D.position t ω a) j))=A.q*coordinateCost A D hk z t ω := by
    simp only [coordinateCost,mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro j _
    simp only [GeometricMass.radius,radius,pow_succ]
    ring
  simp only [sum_add_distrib,←mul_sum,←sum_mul,←sum_div] at hs
  rw [he,HiddenFlow.member_distance] at hs
  dsimp only [driftLog]
  nlinarith only [hs]

end UniformKServer.PartitionTree

end


end

end OAI
