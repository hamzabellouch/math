import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PathRequiredBaseChild
import OAI.Combinatorics.TriangleRemoval.Process.PairRequired

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pathRequired_base_append {A : Type*} [DecidableEq A]
    (base path ex : List A) :
    pathRequired (base.reverse ++ path) (ex ++ base) = pathRequired path ex := by
  simp [pathRequired,List.reverse_append,List.prefix_append_right_inj]

lemma pairRequired_base_child {A : Type*} [DecidableEq A]
    (base : List A) (a b p : A) (as bs : List A) :
    pairRequired (base.reverse ++ a :: as) (base.reverse ++ b :: bs) (p :: base) =
      decide (p = a ∨ p = b) := by
  simp only [pairRequired,pathRequired_base_child]
  by_cases ha : p = a <;> by_cases hb : p = b <;> simp [ha,hb]

section JointPairHelpers
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem jointMarkedQuery_congr_required (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (r s : List (ι × τ) → Bool)
    (hrs : ∀ ex : List (ι × τ), ex ≠ [] → r (ex ++ c.address) = s (ex ++ c.address)) :
    jointMarkedQuery H N r d k c = jointMarkedQuery H N s d k c := by
  induction d generalizing k c with
  | zero => rfl
  | succ d ih =>
    simp only [jointMarkedQuery]
    congr 1
    funext values
    congr 2
    apply List.map_congr_left
    intro p _
    have he := hrs [p.1] (by simp)
    simp only [List.singleton_append] at he
    rw [he]
    congr 1
    split
    · apply ih
      intro ex hex
      simpa only [List.append_assoc,List.singleton_append] using
        hrs (ex ++ [p.1]) (by simp)
    · rfl

theorem jointMarkedQuery_pair_nil (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (path : List (ι × τ)) :
    jointMarkedQuery H N (pairRequired c.address.reverse (c.address.reverse ++ path)) d k c =
      jointMarkedQuery H N (pathRequired (c.address.reverse ++ path)) d k c := by
  apply jointMarkedQuery_congr_required
  intro ex hex
  have hh : pathRequired c.address.reverse (ex ++ c.address) = false := by
    have he := pathRequired_base_append c.address [] ex
    simp only [List.append_nil] at he
    rw [he]
    simp [pathRequired,hex]
  simp only [pairRequired,hh,Bool.false_or]

theorem jointMarkedQuery_pair_child (H : τ → Finset ι) (N d k : ℕ)
    (base : List (ι × τ)) (a b : ι × τ) (as bs : List (ι × τ)) (hab : a ≠ b)
    (focus : Finset ι) (parent : Option τ) :
    jointMarkedQuery H N
        (pairRequired (base.reverse ++ a :: as) (base.reverse ++ b :: bs))
        d k ⟨a :: base,focus,parent⟩ =
      jointMarkedQuery H N (pathRequired ((a :: base).reverse ++ as))
        d k ⟨a :: base,focus,parent⟩ := by
  apply jointMarkedQuery_congr_required
  intro ex _
  simp [pairRequired,pathRequired,List.reverse_append,List.reverse_cons,
    List.append_assoc,List.prefix_append_right_inj,List.cons_prefix_cons,hab]

theorem jointMarkedQuery_hit_head (H : τ → Finset ι) (N d k : ℕ)
    (r : List (ι × τ) → Bool) (ν : τ → PMF (Fin N))
    (base : List (ι × τ)) (p a : ι × τ) (as : List (ι × τ))
    (focus : Finset ι) (parent : Option τ)
    {z : Bool × Bool × List (QueryCall ι τ)}
    (hz : z ∈ (ExposureTree.fresh ν
      (jointMarkedQuery H N r d k ⟨p :: base,focus,parent⟩)).support)
    (hh : ∃ q ∈ z.2.2, q.address = (a :: as).reverse ++ base) : p = a := by
  obtain ⟨q,hq,he⟩ := hh
  have had := jointMarkedQuery_address H N r d k ⟨p :: base,focus,parent⟩ ν hz q hq
  rw [he] at had
  have haa : a :: base <:+ (a :: as).reverse ++ base := by
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    exact List.suffix_append _ _
  exact (List.cons.inj
    ((List.suffix_of_suffix_length_le had haa (by simp)).eq_of_length (by simp))).1

omit [Fintype τ] in
lemma query_trace_cons_hit_tail (c : QueryCall ι τ) (l : List (QueryCall ι τ))
    (a : ι × τ) (as : List (ι × τ))
    (h : ∃ q ∈ c :: l, q.address = (a :: as).reverse ++ c.address) :
    ∃ q ∈ l, q.address = (a :: as).reverse ++ c.address := by
  obtain ⟨q,hq,he⟩ := h
  rcases List.mem_cons.mp hq with rfl | hq
  · have hl := congrArg List.length he
    simp only [List.length_append,List.length_reverse,List.length_cons] at hl
    omega
  · exact ⟨q,hq,he⟩

end JointPairHelpers
end SharpTerminalLeave

end

end OAI
