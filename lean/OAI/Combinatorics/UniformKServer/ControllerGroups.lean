import Mathlib
import OAI.Combinatorics.UniformKServer.ControllerEpoch

namespace OAI

noncomputable section
                                       
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation EpochCut BoundaryPartition

variable {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
  (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ)
  (hN : ∀s r,∑j,N s r j=2^b)

noncomputable def groupExpected : Configuration n k → List (List (Fin n)) → ℝ
  | _,[] => 0
  | s,p::ps => BitSampling.mean (fun coins : Tape k M b =>
      let g := EpochControl.runTrace hk M (selector N hN (extend coins)) (EpochControl.initial u) p
      costAlong d s g+groupExpected (finish s g) ps)

theorem expected_groups (s : Configuration n k) (w : List (Fin n)) :
    expected hk hR d u N hN (initial (M:=M) hR u) s w=
      groupExpected (M:=M) hk d u N hN s (split k R ∅ 0 [] w) := by
  induction w using (measure List.length).wf.induction generalizing s with
  | _ w ih =>
    cases w with
    | nil => simp [expected,split,groupExpected]
    | cons r w =>
      rw [split_cut k R ∅ 0 [] (r::w) (by simp),List.nil_append]
      rw [fresh_mean hk hR d u N hN (initial (M:=M) hR u) rfl]
      rw [groupExpected]
      apply congrArg BitSampling.mean
      funext coins
      rw [cut_expected hk hR d u N hN]
      congr 1
      exact ih _ (tail_shorter k R ∅ 0 r w) _

theorem expected_epochs (s : Configuration n k) (w : List (Fin n)) :
    expected hk hR d u N hN (initial (M:=M) hR u) s w=
      groupExpected (M:=M) hk d u N hN s (EpochPartition.epochs k R hR w) := by
  rw [expected_groups,streamed_epochs]

end UniformKServer.TapeController

end


end

end OAI
