import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionTree

namespace OAI

                                   
section

/-! The multiscale independent partition tape; its law is input-law independent. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset FiniteProbability
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixPL (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairPL : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

def staticLevel (A : ActualPartitions.Config X) (N k j : ℕ) : LevelMap.Data X N (height k) where
  r := GeometricMass.radius A.R A.q j
  positive := GeometricMass.radius_pos A.R A.q A.R_pos A.q_pos j
  K i := TierParameters.cutoff A.C (DyadicTiers.value i.val)
  two i := TierParameters.cutoff_two A.C _ A.C_one (DyadicTiers.one_le_value i.val)
  base := A.base
  center _ := A.base
  heavy _ := False
  qualify _ _ := False

def levelLaw (A : ActualPartitions.Config X) (N k j : ℕ) : Law (LevelTape A k N j) :=
  (staticLevel A N k j).law

def tapeLaw (A : ActualPartitions.Config X) (N k J : ℕ) : Law (Tape A k N J) :=
  Law.pi (fun j=>levelLaw A N k j.val)

theorem levelLaw_actual (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k)
    (hk : 2≤k) (ω : Ω) (j : ℕ) :
    levelLaw A N k j=((A.input (N:=N) (J:=J) D hk ω).level j).data.law := by
  rfl

theorem coordinate_expect (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k)
    (hk : 2≤k) (ω : Ω) (j : Fin J) (f : LevelTape A k N j.val→ℝ) :
    (tapeLaw A N k J).expect (fun z=>f (z j))=
      ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.law.expect f := by
  exact Law.expect_pi_coordinate (fun j : Fin J=>levelLaw A N k j.val) j f

end UniformKServer.PartitionTree

namespace UniformKServer.FiniteProbability
open Finset
variable {Ω : Type*} [Fintype Ω] {I : Type*}
theorem Law.expect_sum (P : Law Ω) (s : Finset I) (f : I→Ω→ℝ) :
    P.expect (fun ω=>∑ i∈s,f i ω)=∑ i∈s,P.expect (f i) := by
  simp only [Law.expect,mul_sum]
  rw [sum_comm]
end UniformKServer.FiniteProbability

end


end

end OAI
