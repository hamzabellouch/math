import Mathlib
import OAI.Combinatorics.UniformKServer.CausalLevel
import OAI.Combinatorics.UniformKServer.ActualPartitions
import OAI.Combinatorics.UniformKServer.CausalShort
import OAI.Combinatorics.UniformKServer.ActualLevelPilot

namespace OAI

                                      
section

/-! Filtration measurability of actual partition keys, anchors, and pilot
parameters, with a common initially sampled finite tape. -/
noncomputable section
namespace UniformKServer.ActualPartitions.Config
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem key_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v)
    (z : LevelMap.Tape ((A.input (N:=N) (J:=J) D hk ω).level j).data) (p : X) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).data.key ((A.input (N:=N) (J:=J) D hk ω).level j).order z t p=
      ((A.input (N:=N) (J:=J) D hk v).level j).data.key ((A.input (N:=N) (J:=J) D hk v).level j).order z t p := by
  let I := ((A.input (N:=N) (J:=J) D hk ω).level j).data
  let V := ((A.input (N:=N) (J:=J) D hk v).level j).data
  exact LevelMap.Data.key_inputs I I.center V.center I.heavy V.heavy I.qualify V.qualify t
    (A.past_centers (J:=J) D hk ω v t he) (A.past_heavy (J:=J) D hk ω v t j he)
    (A.past_qualify (J:=J) D hk ω v t j he) _ z p

theorem anchor_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v)
    (z : LevelMap.Tape ((A.input (N:=N) (J:=J) D hk ω).level j).data)
    (l : LevelMap.Label ((A.input (N:=N) (J:=J) D hk ω).level j).data) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).data.anchor z t l=
      ((A.input (N:=N) (J:=J) D hk v).level j).data.anchor z t l := by
  let I := ((A.input (N:=N) (J:=J) D hk ω).level j).data
  let V := ((A.input (N:=N) (J:=J) D hk v).level j).data
  exact LevelMap.Data.anchor_inputs I I.center V.center I.heavy V.heavy I.qualify V.qualify t
    (A.past_centers (J:=J) D hk ω v t he) (A.past_heavy (J:=J) D hk ω v t j he)
    (A.past_qualify (J:=J) D hk ω v t j he) z l

theorem long_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).longParameter t=
      ((A.input (N:=N) (J:=J) D hk v).level j).longParameter t := by
  unfold PartitionLevel.Input.longParameter
  congr 1
  apply HeavyProcess.centers_inputs
  · intro s hs
    unfold LevelMap.Data.heavyFlag
    apply exists_congr
    intro hN
    exact A.past_heavy (J:=J) D hk ω v t j he ⟨s,hN⟩ hs
  · intro s hs
    unfold LevelMap.Data.point
    split_ifs with hN
    · exact A.past_centers (J:=J) D hk ω v t he ⟨s,hN⟩ hs
    · rfl

theorem short_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v)
    (i : Fin ((A.input (N:=N) (J:=J) D hk ω).level j).height) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).shortParameter i t=
      ((A.input (N:=N) (J:=J) D hk v).level j).shortParameter i t := by
  unfold PartitionLevel.Input.shortParameter
  apply CausalRosters.short_parameter
  · have := ((A.input (N:=N) (J:=J) D hk ω).level j).data.two i
    omega
  · exact A.past_qualify (J:=J) D hk ω v t j he i
  · exact A.past_centers (J:=J) D hk ω v t he

end UniformKServer.ActualPartitions.Config

end


end

end OAI
