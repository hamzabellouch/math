import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianListSemantics

namespace OAI


                                       
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset

 theorem descend_run (R N H K r n : ℕ) (A : RatMatrix r n) (hn : r<n)
    (ha : Audit R N H K r n A) (fs : Frames) (hfs : fs.length+r ≤ R)
    (hv : FramesValid N H fs) (u : ℕ) (out : Row)
    (hu : BoundedRun eState body (stateBound R N H K) u (returned r n A fs) out) :
    ∃ t ≤ 2*r+1, BoundedRun eState body (stateBound R N H K) (t+u) (desc r n A fs) out := by
  induction r generalizing n fs u with
  | zero =>
      obtain ⟨hr,hN,hh,hk⟩ := audit_head ha
      refine ⟨1,by omega,?_⟩
      have hs := desc_size (values A) fs R N H K hr hN hh (by omega) hv
      rw [Nat.add_comm 1 u]
      exact BoundedRun.step hs (down_base n A fs) hu
  | succ r ih =>
      cases n with
      | zero => omega
      | succ n =>
          obtain ⟨hr,hN,hh,hk⟩ := audit_head ha
          have hs := desc_size (values A) fs R N H K hr hN hh (by omega) hv
          by_cases hp : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty
          · let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' hp
            let B := tabulate (Gaussian.residual (values A) p)
            let frame : Frame := (p.val,List.ofFn (values A 0))
            have hframe : FrameValid N H frame := by
              refine ⟨p.isLt.le.trans hN,by simpa only [frame,List.length_ofFn] using hN,?_⟩
              intro q hq
              obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
              exact hh 0 j
            have hvalid : FramesValid N H (frame::fs) := by
              intro f hf
              rcases List.mem_cons.mp hf with rfl|hf
              · exact hframe
              · exact hv f hf
            have hlen : (frame::fs).length+r ≤ R := by simp only [List.length_cons]; omega
            have hB := audit_pivot ha hp
            obtain ⟨hrB,hNB,hhB,hkB⟩ := audit_head hB
            have hrise : BoundedRun eState body (stateBound R N H K) (u+1)
                (returned r n B (frame::fs)) out := by
              apply BoundedRun.step
              · exact up_size (fun j : Fin n => (kernelVector r n B)[j.val]) (frame::fs) R N H K hNB hkB (by omega) hvalid
              · exact return_pivot A fs hp
              · exact hu
            obtain ⟨t,ht,htRun⟩ := ih n B (by omega) hB (frame::fs) hlen hvalid (u+1) hrise
            refine ⟨t+2,by omega,?_⟩
            have hstep := BoundedRun.step hs (down_pivot A fs hp) htRun
            rw [show (t+2)+u=(t+(u+1))+1 by omega]
            exact hstep
          · have hB := audit_skip ha hp
            have hcont : BoundedRun eState body (stateBound R N H K) u
                (returned r (n+1) (tabulate (fun i j => values A i.succ j)) fs) out := by
              rw [return_skip A fs hp]
              exact hu
            obtain ⟨t,ht,htRun⟩ := ih (n+1) (tabulate (fun i j => values A i.succ j)) (by omega) hB fs (by omega) hv u hcont
            refine ⟨t+1,by omega,?_⟩
            have hstep := BoundedRun.step hs (down_skip A fs hp) htRun
            rw [show (t+1)+u=(t+u)+1 by omega]
            exact hstep

 theorem full_run (R N H K r n : ℕ) (A : RatMatrix r n) (hn : r<n)
    (ha : Audit R N H K r n A) :
    ∃ t ≤ 2*r+2, BoundedRun eState body (stateBound R N H K) t (desc r n A []) (kernelList r n A) := by
  obtain ⟨hr,hN,hh,hk⟩ := audit_head ha
  have hv : FramesValid N H [] := by intro f hf; cases hf
  have hend : BoundedRun eState body (stateBound R N H K) 1 (returned r n A []) (kernelList r n A) := by
    apply BoundedRun.stop
    · exact up_size (fun j : Fin n => (kernelVector r n A)[j.val]) [] R N H K hN hk (by simp) hv
    · exact finish r n A
  obtain ⟨t,ht,hrun⟩ := descend_run R N H K r n A hn ha [] (by simpa) hv 1 _ hend
  exact ⟨t+1,by omega,hrun⟩
end MetricKMedian.Gaussian.ListOperation
end

end OAI
