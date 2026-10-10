import Mathlib
import OAI.Combinatorics.UniformKServer.EpochExpectation
import OAI.Combinatorics.UniformKServer.RawRows
import OAI.Combinatorics.UniformKServer.RawControl
import OAI.Combinatorics.UniformKServer.EpochFinite

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawTape
open RawTyped

def tape {H b : ℕ} (coins : Fin H→Fin b→Bool) : List ℕ :=
  List.ofFn (fun i=>(BitSampling.bitsEquiv b (coins i)).val)

theorem zeros (b : ℕ) : (BitSampling.bitsEquiv b (fun _=>false)).val=0 := by
  simp [BitSampling.bitsEquiv,Equiv.trans_apply,finPiFinEquiv_apply,finTwoEquiv]

theorem get_tape {H b : ℕ} (coins : Fin H→Fin b→Bool) (t : ℕ) :
    (tape coins).getD t 0=(BitSampling.bitsEquiv b (EpochExpectation.extend coins t)).val := by
  by_cases h : t<H
  · simp [tape,EpochExpectation.extend,h]
  · rw [List.getD_eq_default _ _ (by simpa [tape] using Nat.le_of_not_gt h)]
    simp [EpochExpectation.extend,h,zeros]

theorem tracking {n k M b : ℕ} (hk : 0<k) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : EpochControl.State n k) (hs : EpochControl.Bounded M s) (r : Fin n)
    (coins : Fin (horizon k M)→Fin b→Bool) :
    RawControl.trackingLabel k T (tape coins) (RawControl.state s) r.val=
      (EpochExpectation.selector (RawRows.complete hk (horizon k M) b T)
        (RawRows.total hk hT) (EpochExpectation.extend coins) s.filter.kept s.virtual.position r).val := by
  have hp : s.filter.kept.length≤horizon k M := by
    have h₁:=hs.1.2.1
    have h₂:=hs.1.2.2
    omega
  unfold RawControl.trackingLabel
  simp only [RawControl.state,RawFilter.state,RawFilter.entry,requests,List.length_map,get_tape]
  exact RawRowSelect.choose_eq T s.filter.kept s.virtual.position r
    (RawRows.complete hk (horizon k M) b T (s.filter.kept,s.virtual.position) r)
    (by intro j;simp only [RawRows.complete,ite_eq_left hp,RawExpansion.kernel])
    (RawRows.total hk hT _ _) _

end UniformKServer.RawTape

end


end

end OAI
