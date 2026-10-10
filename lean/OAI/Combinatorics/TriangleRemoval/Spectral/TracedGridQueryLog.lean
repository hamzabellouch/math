import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.FreshLogExposeLabeled

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section TraceAccounting
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem tracedGridQuery_log (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    z.2 = z.1.2.flatMap (QueryCall.keys H) := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by
      simpa [ExposureTree.freshLog] using hy
    have hkeys := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).2
    simp [heq, hkeys, QueryCall.keys]
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxkeys := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).2
    have hwkeys := ExposureTree.freshLog_checkNoneTrace_support ν (QueryCall.keys H) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · exact ih _ _ ha
        · have heq : a = ((false,[]),[]) := by
            simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    simp only [List.flatMap_cons, hxkeys, hwkeys, QueryCall.keys]

end TraceAccounting
end SharpTerminalLeave

end

end OAI
