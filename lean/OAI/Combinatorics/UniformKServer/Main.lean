import Mathlib
import OAI.Combinatorics.UniformKServer.MetricRealization
import OAI.Combinatorics.UniformKServer.PartitionCausal
import OAI.Combinatorics.UniformKServer.LevelErrorMass
import OAI.Combinatorics.UniformKServer.ScaleAllowances
import OAI.Combinatorics.UniformKServer.RoundingKernel
import OAI.Combinatorics.UniformKServer.ClockSchedule
import OAI.Combinatorics.UniformKServer.RawSearch
import OAI.Combinatorics.UniformKServer.RawControllerCost
import OAI.Combinatorics.UniformKServer.WrapperStartup
import OAI.Combinatorics.UniformKServer.WrapperDelayed
import OAI.Combinatorics.UniformKServer.WrapperReachable

namespace OAI

noncomputable section

namespace UniformKServer
open UniformWrapper TypedStack
open scoped Classical

/-- The literal finite-control wrapper is a single horizon-free online machine.
The very large verified constructor is paid only through a finite, instance-
dependent initial delay; each request still takes the fixed linear bit budget. -/
theorem uniform_squared_logarithmic_main : UniformAlgorithmClaim := by
  let mult : ℕ := ⌈PartitionTree.absoluteRate⌉₊
  have hm : PartitionTree.absoluteRate≤(mult:ℝ) := Nat.le_ceil _
  refine ⟨machine mult,64,1,OffsetInstance.coefficient mult,by norm_num,
    OffsetInstance.coefficient_positive mult,?_⟩
  intro n k hn hk hkn d s
  let : NeZero k := ⟨by omega⟩
  have hk0 : 0<k:=by omega
  have hkle : k≤n:=by omega
  let draw := (RawBinary.distances d).map RawMetric.present
  have hdr : ∀x y : Fin n,RawArithmetic.value (RawTable.dist n draw x.val y.val)=d.distance x y :=
    RawBinary.metric_input d
  have hx:=ConstructorSearch.exists_certificate (by omega : 2≤n) hk hkle mult hm d draw hdr
  have hdom:=ConstructorSearch.terminates hx
  let v:=(ConstructorSearch.search mult (n,k,draw)).get hdom
  have hvs : v∈ConstructorSearch.search mult (n,k,draw):=Part.get_mem hdom
  have hv:=ConstructorSearch.correct hvs
  simp only [ConstructorSearch.verify,Bool.and_eq_true_iff] at hv
  have hp:=RawAccepted.spec d draw hdr hv.1
  let a:=RawBinary.value (instanceCode d s++[true])
  have hi : ConstructorProgram.read a=(n,k,draw):=ConstructorProgram.read_code d s
  have hs : v∈ConstructorSearch.search mult (ConstructorProgram.read a) := by rw [hi];exact hvs
  obtain ⟨delay,hd,⟨p⟩⟩:=startup_exists mult a v hs
  simp only [hi] at p
  have hb:=boot_core mult d s
  have hz : CoreRep (uniform mult) (p.state 0) (boot (machine mult) 64 1 d s) := by
    rw [p.start]
    exact hb
  refine ⟨hb.yielded,?_,?_⟩
  · intro t z hreach r coins
    have hl:=all_reachable mult hk0 hkle v.1 hp.numbers.restart_pos hp.rows v.2 hv.2 delay hd _ p d s hb t z hreach
    exact (live_next mult (instanceCode d s).length hk0 hkle v.1 hp.numbers.restart_pos hp.rows
      v.2 hv.2 delay hd _ p t z hl r coins).2
  · obtain ⟨B,hB,hcost⟩:=RawControllerCost.delayed_bound hk hkle hm d draw hdr v.1 hv.1 s delay
    refine ⟨B,hB,?_⟩
    intro w
    have he:=prefix_expected mult (instanceCode d s).length hkle v.1 hp.numbers.restart_pos hp.rows
      v.2 hv.2 delay hd _ p d w 0 (Nat.zero_le _) (boot (machine mult) 64 1 d s) hz s
    have he' : machineExpectedCost (machine mult) 64 1 (instanceCode d s).length d hk0
        0 (boot (machine mult) 64 1 d s) s w=
        RawControllerCost.delayed hkle d draw hdr v.1 hv.1 s delay w := by
      simpa only [Nat.sub_zero,RawControllerCost.delayed,RawControllerCost.expected,RawControllerCost.N,
        RawControllerCost.u,tcExpected,tcInitial,tcRows,tcN] using he
    exact he'.trans_le (hcost w)

end UniformKServer

end

end OAI
