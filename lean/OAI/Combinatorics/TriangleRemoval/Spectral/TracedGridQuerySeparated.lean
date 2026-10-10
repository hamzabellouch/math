import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.TracedGridQueryLog
import OAI.Combinatorics.TriangleRemoval.Queries.Separated
import OAI.Combinatorics.TriangleRemoval.Spectral.FreshLogCheckNone

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
section TrueRepeatedCall
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem tracedGridQuery_separated (H : τ → Finset ι)
    (hlin : ∀ T S, T ≠ S → (H T ∩ H S).card ≤ 1)
    (N d k : ℕ) (c : QueryCall ι τ) (hc : c.Separated H)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    ∀ a ∈ z.1.2, a.Separated H := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    simpa [heq] using hc
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hwP := ExposureTree.freshLog_checkNoneTrace_forall ν (fun a => a.Separated H) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · exact ih _ _ (separated_child H hlin _ _ _) ha
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc
    · exact hwP a ha

theorem repeated_flatMap_calls {R K : Type*} [DecidableEq K]
    (calls : List R) (keys : R → List K)
    (hc : ∀ c ∈ calls, (keys c).Nodup)
    (hr : ExposureTree.repeats ∅ (calls.flatMap keys) = true) :
    ∃ i j : Fin calls.length, i < j ∧ ∃ T,
      T ∈ keys (calls.get i) ∧ T ∈ keys (calls.get j) := by
  by_contra hn
  have hnd : (calls.flatMap keys).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨hc, List.pairwise_iff_get.mpr ?_⟩
    intro i j hij
    apply List.disjoint_left.mpr
    intro T hTi hTj
    exact hn ⟨i,j,hij,T,hTi,hTj⟩
  have hf := (ExposureTree.repeats_empty_false_iff _).mpr hnd
  rw [hr] at hf
  contradiction

theorem tracedGridQuery_repeat_calls (H : τ → Finset ι)
    (hlin : ∀ T S, T ≠ S → (H T ∩ H S).card ≤ 1)
    (N d k : ℕ) (c : QueryCall ι τ) (hc : c.Separated H)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support)
    (hr : ExposureTree.repeats ∅ z.2 = true) :
    ∃ i j : Fin z.1.2.length, i < j ∧ ∃ T,
      T ∈ (z.1.2.get i).keys H ∧ T ∈ (z.1.2.get j).keys H := by
  have hp := tracedGridQuery_separated H hlin N d k c hc ν hz
  rw [tracedGridQuery_log H N d k c ν hz] at hr
  exact repeated_flatMap_calls _ _ (fun a ha => a.keys_nodup H (hp a ha)) hr

end TrueRepeatedCall
end SharpTerminalLeave

end

end OAI
