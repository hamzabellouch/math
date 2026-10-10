import Mathlib
import OAI.Combinatorics.UniformKServer.HiddenTesting
import OAI.Combinatorics.UniformKServer.ActualEditCosts
import OAI.Combinatorics.UniformKServer.ActualCoordinate

namespace OAI

noncomputable section

/-! True post-request filtering tests of literal integrated key edits. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixEI (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairEI : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

theorem diff_indicator {B : Type*} (a b : B) : PrefixMovement.diff a b=FirstStructure.indicator b a := by
  unfold PrefixMovement.diff FirstStructure.indicator
  simp only [eq_comm]

theorem integrated_edit (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) (j : Fin J) (p : X) :
    (tapeLaw A N k J).expect (fun z=>GeometricMass.radius A.R A.q j.val*PrefixMovement.diff
      (word A D hk z (n.val+1) ω p j) (word A D hk z n.val ω p j))=
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.editCost n
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order p := by
  rw [Law.expect_mul]
  simp_rw [diff_indicator]
  exact congrArg (fun x=>GeometricMass.radius A.R A.q j.val*x) (coordinate_expect (N:=N) A D hk ω j
    (fun zz=>FirstStructure.indicator
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order zz n.val p)
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order zz (n.val+1) p)))

theorem edit_measurable (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (n : Fin N) (j : Fin J) (ω v : Ω) (h : (D.filtration (n.val+1)).r ω v) :
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.editCost n
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order =
    ((A.input (N:=N) (J:=J) D hk v).level j.val).data.editCost n
        ((A.input (N:=N) (J:=J) D hk v).level j.val).order := by
  funext p
  rw [←integrated_edit A D hk ω n j p,←integrated_edit A D hk v n j p]
  congr 1
  funext z
  apply congrArg (fun x=>GeometricMass.radius A.R A.q j.val*x)
  exact congrArg₂ PrefixMovement.diff
    (A.key_measurable (N:=N) (J:=J) D hk ω v (n.val+1) j.val h (z j) p)
    (A.key_measurable (N:=N) (J:=J) D hk ω v n.val j.val (D.refines n.val ω v h) (z j) p)

theorem edits_expect (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (n : Fin N) :
    average D.weight (fun ω=>(tapeLaw A N k J).expect (fun z=>pathEdits A D hk z n.val ω))=
      average D.weight (A.keyEditCost (N:=N) (J:=J) D hk n.val) := by
  have hp (ω : Ω) : (tapeLaw A N k J).expect (fun z=>pathEdits A D hk z n.val ω)=
      ∑ j : Fin J,∑ a : Fin k,
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.editCost n
          ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (D.position n.val ω a) := by
    unfold pathEdits
    simp_rw [Law.expect_sum]
    rw [sum_comm]
    exact sum_congr rfl (fun j _=>sum_congr rfl (fun a _=>integrated_edit A D hk ω n j _))
  simp_rw [hp]
  unfold ActualPartitions.Config.keyEditCost
  simp only [dite_eq_left n.isLt]
  simp only [←Fin.sum_univ_eq_sum_range]
  have hs (f : Fin J→Ω→ℝ) : average D.weight (fun ω=>∑ j,f j ω)=∑ j,average D.weight (f j) := by
    unfold average
    simp only [mul_sum]
    rw [sum_comm]
  rw [hs,hs]
  apply sum_congr rfl
  intro j _
  exact (HiddenFlow.filtered_test D n.val _ (edit_measurable A D hk n j)).symm

end UniformKServer.PartitionTree

end

end OAI
