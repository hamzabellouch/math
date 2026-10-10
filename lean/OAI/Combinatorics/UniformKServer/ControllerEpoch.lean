import Mathlib
import OAI.Combinatorics.UniformKServer.TapeController
import OAI.Combinatorics.UniformKServer.EpochCut

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation EpochCut

variable {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
  (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ)
  (hN : ∀s r,∑j,N s r j=2^b)

/-- Deterministic evolution under the already loaded epoch tape, up to the next
raw-block boundary. No future requests are needed by the controller. -/
theorem cut_expected (z : State n k M R b) (s : Configuration n k)
    (coins : Tape k M b) (w : List (Fin n)) :
    let parts := cut k R z.localState.val.seen z.completed.val w
    let g := EpochControl.runTrace hk M (selector N hN (extend coins)) z.localState.val parts.1
    expected hk hR d u N hN (loaded z coins) s w = costAlong d s g+
      expected hk hR d u N hN (initial (M:=M) hR u) (finish s g) parts.2 := by
  induction w generalizing z s with
  | nil => simp [cut,EpochControl.runTrace,costAlong,expected]
  | cons r w ih =>
    dsimp only
    rw [loaded_cons]
    have hl : choose hk N hN (loaded z coins) r coins=
      EpochControl.label hk (selector N hN (extend coins)) z.localState.val r := rfl
    rw [hl]
    by_cases hb : boundary z r
    · have hb' : boundary (loaded z coins) r := hb
      simp only [cut,show k<(insert r z.localState.val.seen).card ∧ z.completed.val+1=R from hb,
        ite_eq_left,step,dite_eq_left hb']
      simp [EpochControl.runTrace,costAlong,finish]
    · have hb' : ¬boundary (loaded z coins) r := hb
      let z' := step hk hR u N hN (loaded z coins) r coins
      have hloc : z'.localState.val=EpochControl.step hk M (selector N hN (extend coins)) z.localState.val r := by
        simp only [z',step,dite_eq_right hb']
        rfl
      have hseen : z'.localState.val.seen=bookStep (k:=k) z.localState.val.seen r := by
        rw [hloc,step_seen]
      have hcomp : z'.completed.val=z.completed.val+if k<(insert r z.localState.val.seen).card then 1 else 0 := by
        simp only [z',step,dite_eq_right hb']
        rfl
      have hload : loaded z' coins=z' := by
        simp only [z',step,dite_eq_right hb']
        rfl
      have hh := ih z' (serve s r (EpochControl.label hk (selector N hN (extend coins)) z.localState.val r))
      dsimp only at hh
      rw [hload,hseen,hcomp,hloc] at hh
      simp only [cut,show ¬(k<(insert r z.localState.val.seen).card ∧ z.completed.val+1=R) from hb,ite_false,EpochControl.runTrace,costAlong,finish]
      change _+expected hk hR d u N hN z' _ w=_
      rw [hh]
      simp only [add_assoc]

end UniformKServer.TapeController

end


end

end OAI
