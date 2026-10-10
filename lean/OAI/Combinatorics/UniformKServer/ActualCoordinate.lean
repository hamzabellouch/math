import Mathlib
import OAI.Combinatorics.UniformKServer.PilotTemplates
import OAI.Combinatorics.UniformKServer.PartitionMovement
import OAI.Combinatorics.UniformKServer.PartitionLaw
import OAI.Combinatorics.UniformKServer.FlowAuxiliary

namespace OAI

noncomputable section

/-! Literal coordinate-key motion split into actual edits and the one mover. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixAC (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAC : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

theorem diff_triangle {B : Type*} (a b c : B) :
    PrefixMovement.diff a c≤PrefixMovement.diff a b+PrefixMovement.diff b c := by
  unfold PrefixMovement.diff
  split_ifs <;> norm_num
  aesop

def pathEdits (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Fin k,∑ j : Fin J,GeometricMass.radius A.R A.q j.val*PrefixMovement.diff
    (word A D hk z (t+1) ω (D.position t ω a) j) (word A D hk z t ω (D.position t ω a) j)

def pathMove (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin J,GeometricMass.radius A.R A.q j.val*PrefixMovement.diff
    (word A D hk z (t+1) ω (D.request t ω) j)
    (word A D hk z (t+1) ω (D.position t ω (D.chosen t ω)) j)

theorem coordinate_split (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) :
    A.q*coordinateCost A D hk z t ω≤pathEdits A D hk z t ω+pathMove A D hk z t ω := by
  have hr (j : Fin J) : A.q*radius A j.val=GeometricMass.radius A.R A.q j.val := by
    unfold radius GeometricMass.radius
    rw [pow_succ]
    ring
  have h1 := sum_le_sum (fun a (_ : a∈(univ : Finset (Fin k)))=>
    sum_le_sum (fun j (_ : j∈(univ : Finset (Fin J)))=>
      mul_le_mul_of_nonneg_left (diff_triangle
        (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
        (word A D hk z (t+1) ω (D.position t ω a) j)
        (word A D hk z t ω (D.position t ω a) j))
        (GeometricMass.radius_pos A.R A.q A.R_pos A.q_pos j.val).le))
  have he (a : Fin k) : (∑ j : Fin J,GeometricMass.radius A.R A.q j.val*PrefixMovement.diff
      (word A D hk z (t+1) ω (D.position (t+1) ω a) j)
      (word A D hk z (t+1) ω (D.position t ω a) j))=
      if a=D.chosen t ω then pathMove A D hk z t ω else 0 := by
    rw [D.update]
    split_ifs with ha
    · subst a; rfl
    · simp [PrefixMovement.diff]
  simp only [mul_add,sum_add_distrib,he,sum_ite_eq',mem_univ,ite_true] at h1
  unfold coordinateCost
  simp only [mul_sum,←mul_assoc,hr]
  dsimp only [pathEdits] at *
  linarith only [h1]

theorem move_expect (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) :
    (tapeLaw A N k J).expect (fun z=>pathMove A D hk z n.val ω)≤
      (A.input (N:=N) (J:=J) D hk ω).coefficient*(1+Real.log k)*
        dist (D.request n.val ω) (D.position n.val ω (D.chosen n.val ω)) := by
  unfold pathMove
  rw [Law.expect_sum]
  simp only [Law.expect_mul]
  have he (j : Fin J) :
      (tapeLaw A N k J).expect (fun z=>PrefixMovement.diff
        (word A D hk z (n.val+1) ω (D.request n.val ω) j)
        (word A D hk z (n.val+1) ω (D.position n.val ω (D.chosen n.val ω)) j))=
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).separation n
          (D.position n.val ω (D.chosen n.val ω)) := by
    change (tapeLaw A N k J).expect (fun z=>FirstStructure.indicator
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) (n.val+1) (D.request n.val ω))
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) (n.val+1)
          (D.position n.val ω (D.chosen n.val ω))))=_
    unfold PartitionLevel.Input.separation
    exact coordinate_expect (N:=N) A D hk ω j (fun zz=>FirstStructure.indicator
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order zz (n.val+1) (D.request n.val ω))
      (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
        ((A.input (N:=N) (J:=J) D hk ω).level j.val).order zz (n.val+1)
          (D.position n.val ω (D.chosen n.val ω))))
  simp_rw [he]
  simpa only [←Fin.sum_univ_eq_sum_range,PartitionScales.Input.level,ActualPartitions.Config.input] using A.separation (J:=J) D hk ω n (D.position n.val ω (D.chosen n.val ω))

end UniformKServer.PartitionTree

end

end OAI
