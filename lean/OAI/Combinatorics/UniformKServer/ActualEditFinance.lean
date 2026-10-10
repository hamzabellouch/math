import Mathlib
import OAI.Combinatorics.UniformKServer.ActualEditCosts

namespace OAI

noncomputable section

/-! Integrated height-free key edits, financed by actual posterior pilots. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

omit [Fintype X] [MetricSpace X] in
theorem editRate_nonneg (A : Config X) : 0≤A.editRate := by
  have hγ := A.P.gammaH_pos
  have hδ : 0<Real.log (1+A.P.deltaH) := Real.log_pos (by linarith [A.P.deltaH_pos])
  unfold editRate
  have hC : 0≤8*A.C+24 := by linarith [A.C_one]
  positivity

def editBound (A : Config X) : ℝ := 147*PilotFamily.rateBound A.P+A.editRate

def editEndpoint (A : Config X) (k J : ℕ) : ℝ :=
  882*k*(∑ j∈range J,GeometricMass.radius A.R A.q j)+k*A.auxiliaryCap k J

theorem edit_finance (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) :
    (∑ t∈range N,average D.weight (A.keyEditCost (N:=N) (J:=J) D hk t))≤
      A.editBound*(1+Real.log (k+1))*(∑ t∈range N,average D.weight (moverCost (HiddenFlow.flow D) t))+
      A.editEndpoint k J := by
  let F := HiddenFlow.flow D
  let Q := ∑ t∈range N,average D.weight (moverCost F t)
  have hQ : 0≤Q := sum_nonneg (fun t _=>sum_nonneg (fun ω _=>mul_nonneg (D.positive ω).le
    (sum_nonneg (fun p _=>mul_nonneg (F.mover_nonneg t ω p) dist_nonneg))))
  have he := linear_edits F N (A.auxiliary (N:=N) (J:=J) D hk) (A.auxiliaryCap k J)
    (A.auxiliary_bounds D hk) (A.auxiliary_measurable D hk)
    (A.keyEditCost (N:=N) (J:=J) D hk)
    (fun t ω=>147*A.totalPilotCharge (N:=N) (J:=J) D hk t ω+A.editRate*(1+Real.log k)*moverCost F t ω)
    (fun t ht ω=>A.key_mass_step D hk ω ⟨t,ht⟩)
  simp only [average_add,average_smul,sum_add_distrib,←mul_sum] at he
  have hp := A.pilot_finance (N:=N) (J:=J) D hk N
  have hl : 0≤1+Real.log (k+1) := by
    have h : (1:ℝ)≤k+1 := by have := Nat.cast_nonneg (α:=ℝ) k; linarith
    linarith [Real.log_nonneg h]
  have hr := mul_le_mul_of_nonneg_right (PilotFamily.rate_bound A.P k) (mul_nonneg hl hQ)
  have hm := mul_le_mul_of_nonneg_left (PilotFamily.weight_sum k)
    (show 0≤(2:ℝ)*k*(∑ j∈range J,GeometricMass.radius A.R A.q j) by
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (sum_nonneg (fun j _=> (GeometricMass.radius_pos A.R A.q A.R_pos A.q_pos j).le)))
  have hlog : 1+Real.log k≤1+Real.log (k+1) := by
    have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    linarith [Real.log_le_log hk' (show (k:ℝ)≤k+1 by linarith)]
  have hg := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog A.editRate_nonneg) hQ
  change (∑ t∈range N,average D.weight (A.keyEditCost (N:=N) (J:=J) D hk t))≤
    147*(∑ t∈range N,average D.weight (A.totalPilotCharge (N:=N) (J:=J) D hk t))+
      A.editRate*(1+Real.log k)*Q+k*A.auxiliaryCap k J at he
  change (∑ t∈range N,average D.weight (A.totalPilotCharge (N:=N) (J:=J) D hk t))≤
    (∑ i : PilotFamily.Index k,PilotFamily.weight i*rate (PilotFamily.template A.P i))*(1+Real.log (k+1))*Q+_ at hp
  unfold editBound editEndpoint
  dsimp only [Q] at *
  nlinarith only [he,hp,hr,hm,hg]

end UniformKServer.ActualPartitions.Config

end

end OAI
