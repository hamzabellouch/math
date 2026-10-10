import Mathlib
import OAI.Combinatorics.UniformKServer.ActualPartitions
import OAI.Combinatorics.UniformKServer.ActualLevelPilot
import OAI.Combinatorics.UniformKServer.PartitionCausal
import OAI.Combinatorics.UniformKServer.PilotFamily
import OAI.Combinatorics.UniformKServer.ReverseScales

namespace OAI

noncomputable section

/-! The global pilot finance ledger for the literal partition. Constants do not
 depend on the input law, time horizon, or the number of scales. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits PilotCompact
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def pilotParameter (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) : X→ℝ :=
  if j<J then match i with
    | none => ((A.input (N:=N) (J:=J) D hk ω).level (J-1-j)).longParameter t
    | some a => ((A.input (N:=N) (J:=J) D hk ω).level (J-1-j)).shortParameter a t
  else fun _ => 0

def pilotCharge (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) : ℝ :=
  match i with
    | none => ((A.input (N:=N) (J:=J) D hk ω).level j).longCharge t
    | some a => ((A.input (N:=N) (J:=J) D hk ω).level j).shortCharge a t

theorem pilot_bounds (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) (p : X) :
    A.pilotParameter (N:=N) (J:=J) D hk t ω i j p∈Set.Icc (0:ℝ) 1 := by
  unfold pilotParameter
  split_ifs with hj
  · cases i with
    | none => exact PartitionLevel.Input.long_bounds _ _ _
    | some a => exact PartitionLevel.Input.short_bounds _ _ _ _
  · constructor <;> norm_num

theorem pilot_lip (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) (p q : X) :
    |A.pilotParameter (N:=N) (J:=J) D hk t ω i j p-A.pilotParameter (N:=N) (J:=J) D hk t ω i j q|≤
      (PilotFamily.template A.P i).L*(dist p q/((A.R*A.q^J)*(A.q⁻¹)^j)) := by
  by_cases hj : j<J
  · have hr := GeometricMass.radius_reverse A.R A.q A.q_pos.ne' J j hj
    simp only [pilotParameter,ite_eq_left hj]
    cases i with
    | none =>
      change _≤1*(dist p q/((A.R*A.q^J)*(A.q⁻¹)^j))
      rw [one_mul,←hr]
      exact PartitionLevel.Input.long_lip _ _ _ _
    | some a =>
      change _≤8*(dist p q/((A.R*A.q^J)*(A.q⁻¹)^j))
      rw [←hr]
      exact PartitionLevel.Input.short_lip _ _ _ _ _
  · simp only [pilotParameter,ite_eq_right hj,sub_self,abs_zero]
    exact mul_nonneg (PilotFamily.template A.P i).L_nonneg
      (div_nonneg dist_nonneg (mul_nonneg (mul_nonneg A.R_pos.le (pow_nonneg A.q_pos.le _))
        (pow_nonneg (inv_nonneg.mpr A.q_pos.le) _)))

theorem pilot_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) (i : PilotFamily.Index k) (j : ℕ) :
    A.pilotParameter (N:=N) (J:=J) D hk t ω i j=A.pilotParameter (N:=N) (J:=J) D hk t v i j := by
  unfold pilotParameter
  split_ifs with hj
  · cases i with
    | none => exact A.long_measurable D hk ω v t (J-1-j) he
    | some a => exact A.short_measurable D hk ω v t (J-1-j) he a
  · rfl

theorem pilot_charge_nonneg (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) :
    0≤A.pilotCharge (N:=N) (J:=J) D hk t ω i j := by
  cases i with
  | none => exact PartitionLevel.Input.long_charge_nonneg _ _
  | some a => exact PartitionLevel.Input.short_charge_nonneg _ _ _

theorem pilot_payment (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) (hj : j<J) :
    A.pilotCharge (N:=N) (J:=J) D hk t ω i (J-1-j)≤
      PilotFamily.weight i*(
        value ((A.R*A.q^J)*(A.q⁻¹)^j) (PilotFamily.template A.P i).sigma (PilotFamily.template A.P i).R
          (HiddenFlow.current D (t+1) ω) (A.pilotParameter (N:=N) (J:=J) D hk t ω i j)-
        value ((A.R*A.q^J)*(A.q⁻¹)^j) (PilotFamily.template A.P i).sigma (PilotFamily.template A.P i).R
          (HiddenFlow.current D (t+1) ω) (A.pilotParameter (N:=N) (J:=J) D hk (t+1) ω i j)) := by
  rw [←GeometricMass.radius_reverse A.R A.q A.q_pos.ne' J j hj]
  simp only [pilotParameter,ite_eq_left hj]
  cases i with
  | none =>
    change _≤1*(_-_)
    rw [one_mul]
    exact PartitionLevel.Input.long_payment _ t _ (fun _ => rfl)
  | some a =>
    exact PartitionLevel.Input.short_payment ((A.input (N:=N) (J:=J) D hk ω).level (J-1-j)) a
      (A.lifetime_large D hk ω (J-1-j) a) t _ (fun _ => rfl)

def totalPilotCharge (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) : ℝ := ∑ i : PilotFamily.Index k, ∑ j∈range J,
      A.pilotCharge (N:=N) (J:=J) D hk t ω i j

theorem total_pilot_payment (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) :
    A.totalPilotCharge (N:=N) (J:=J) D hk t ω≤
      potential (PilotFamily.template A.P) PilotFamily.weight (A.R*A.q^J) A.q⁻¹ J
        (HiddenFlow.current D (t+1) ω) (A.pilotParameter (N:=N) (J:=J) D hk t ω)-
      potential (PilotFamily.template A.P) PilotFamily.weight (A.R*A.q^J) A.q⁻¹ J
        (HiddenFlow.current D (t+1) ω) (A.pilotParameter (N:=N) (J:=J) D hk (t+1) ω) := by
  simp only [potential,totalPilotCharge,←sum_sub_distrib,←mul_sub,Finset.mul_sum]
  apply sum_le_sum
  intro i _
  rw [←GeometricMass.reverse_sum (fun j => A.pilotCharge (N:=N) (J:=J) D hk t ω i j) J]
  exact sum_le_sum fun j hj => A.pilot_payment D hk t ω i j (mem_range.mp hj)

theorem pilot_finance (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k) (H : ℕ) :
    (∑ t∈range H, average D.weight (A.totalPilotCharge (N:=N) (J:=J) D hk t))≤
      (∑ i : PilotFamily.Index k, PilotFamily.weight i*rate (PilotFamily.template A.P i)) *
        (1+Real.log (k+1))*(∑ t∈range H, average D.weight (moverCost (HiddenFlow.flow D) t)) +
      2*k*(∑ i : PilotFamily.Index k, PilotFamily.weight i)*(∑ j∈range J, GeometricMass.radius A.R A.q j) := by
  have hτ : 2≤A.q⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ A.q_pos).mpr
    linarith [A.q_small]
  have he := pilot_edits hk (HiddenFlow.flow D) (PilotFamily.template A.P) PilotFamily.weight
    PilotFamily.weight_nonneg (A.R*A.q^J) A.q⁻¹ (mul_pos A.R_pos (pow_pos A.q_pos _)) hτ J H
    (A.pilotParameter (N:=N) (J:=J) D hk)
    (A.pilot_bounds D hk) (A.pilot_lip D hk)
    (fun t i j ω v h => A.pilot_measurable D hk t ω v h i j)
    (A.totalPilotCharge (N:=N) (J:=J) D hk)
    (fun t ω => sum_nonneg fun i _ => sum_nonneg fun j _ => A.pilot_charge_nonneg D hk t ω i j)
    (A.total_pilot_payment D hk)
  have hs : (∑ j∈range J, (A.R*A.q^J)*(A.q⁻¹)^j)=∑ j∈range J, GeometricMass.radius A.R A.q j := by
    calc
      _ = ∑ j∈range J, GeometricMass.radius A.R A.q (J-1-j) :=
        sum_congr rfl fun j hj => (GeometricMass.radius_reverse A.R A.q A.q_pos.ne' J j (mem_range.mp hj)).symm
      _ = _ := GeometricMass.reverse_sum _ _
  simpa only [hs,HiddenFlow.flow] using he

end UniformKServer.ActualPartitions.Config

end

end OAI
