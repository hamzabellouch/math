import Mathlib
import OAI.Combinatorics.UniformKServer.ActualPartitions
import OAI.Combinatorics.UniformKServer.PilotTemplates
import OAI.Combinatorics.UniformKServer.CausalLevelAux
import OAI.Combinatorics.UniformKServer.FlowAuxiliary

namespace OAI

noncomputable section

/-! Adapted linear auxiliary family for the literal multiscale partition. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def auxiliary (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (p : X) : ℝ :=
  ∑ j∈range J,((A.input (N:=N) (J:=J) D hk ω).level j).data.auxiliary
    ((A.input (N:=N) (J:=J) D hk ω).level j).order t p

def auxiliaryCap (A : Config X) (k J : ℕ) : ℝ :=
  (1+((DyadicTiers.last (Real.log k)+1:ℕ):ℝ))*(∑ j∈range J,GeometricMass.radius A.R A.q j)

theorem level_auxiliary_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v) (p : X) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).data.auxiliary ((A.input (N:=N) (J:=J) D hk ω).level j).order t p=
      ((A.input (N:=N) (J:=J) D hk v).level j).data.auxiliary ((A.input (N:=N) (J:=J) D hk v).level j).order t p := by
  let I := ((A.input (N:=N) (J:=J) D hk ω).level j).data
  let V := ((A.input (N:=N) (J:=J) D hk v).level j).data
  exact LevelMap.Data.auxiliary_inputs I I.center V.center I.heavy V.heavy I.qualify V.qualify t
    (A.past_centers (J:=J) D hk ω v t he) (A.past_heavy (J:=J) D hk ω v t j he)
    (A.past_qualify (J:=J) D hk ω v t j he) _ p

theorem auxiliary_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) :
    A.auxiliary (N:=N) (J:=J) D hk t ω=A.auxiliary (N:=N) (J:=J) D hk t v := by
  funext p
  apply sum_congr rfl
  intro j _
  exact A.level_auxiliary_measurable D hk ω v t j he p

theorem auxiliary_bounds (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (p : X) :
    0≤A.auxiliary (N:=N) (J:=J) D hk t ω p ∧
      A.auxiliary (N:=N) (J:=J) D hk t ω p≤A.auxiliaryCap k J := by
  let I := A.input (N:=N) (J:=J) D hk ω
  have hb (j : ℕ) := (I.level j).data.auxiliary_bounds (I.level j).order t p
  constructor
  · exact sum_nonneg (fun j _=>(hb j).1)
  · unfold auxiliary auxiliaryCap
    have h := sum_le_sum (s:=range J) (fun j _=>(hb j).2)
    convert h using 1
    dsimp only [I] at *
    simp only [PartitionLevel.Input.order,List.length_ofFn,PartitionLevel.Input.height,
      PartitionScales.Input.level,ActualPartitions.Config.input,PartitionLevel.Input.data,←sum_mul]
    ring

end UniformKServer.ActualPartitions.Config

end

end OAI
