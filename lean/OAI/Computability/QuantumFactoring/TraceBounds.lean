import Mathlib
import OAI.Computability.QuantumFactoring.AuxiliaryProducer

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma list_map_sum_le {α : Type*} (xs : List α) (f g : α→ℕ) (h : ∀ a∈xs,f a ≤ g a) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    exact Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

namespace Logged
variable {Q α β : Type*}

lemma traverse_requests_length (f : α→Logged Q β) (xs : List α) :
    (traverse f xs).requests.length  ≤  (xs.map (fun a => (f a).requests.length)).sum := by
  induction xs with
  | nil => simp [traverse,pure]
  | cons a as ih =>
    cases hx : (f a).result with
    | none => simp [traverse,bind,hx]
    | some b =>
      simp only [traverse,bind,hx,List.length_append,map_requests,List.map_cons,List.sum_cons]
      exact Nat.add_le_add_left ih _

end Logged
namespace AuxiliaryTree

def visits : ℕ→ℕ→List ℕ
  | 0, _ => []
  | depth+1, m => m::(children m).flatMap (visits depth)

lemma sum_map_range (xs : List ℕ) (f : ℕ→ℕ→ℕ) (d : ℕ) :
    (xs.map (fun a => ∑ k∈Finset.range d, f a k)).sum =
      ∑ k∈Finset.range d, (xs.map (fun a => f a k)).sum := by
  induction xs with
  | nil => simp
  | cons a as ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

lemma visits_length (depth m : ℕ) :
    (visits depth m).length = ∑ k∈Finset.range depth, (level m k).length := by
  induction depth generalizing m with
  | zero => simp [visits]
  | succ d ih =>
    rw [visits,List.length_cons,List.length_flatMap]
    simp_rw [ih]
    rw [sum_map_range,Finset.sum_range_succ']
    simp only [level,List.length_flatMap,List.length_singleton]

lemma visits_length_le {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (depth : ℕ) :
    (visits depth m).length  ≤  depth*n := by
  rw [visits_length]
  calc
    _  ≤  ∑ _k∈Finset.range depth,n := Finset.sum_le_sum (fun k _ => (level_length_lt (k:=k) hm hb).le)
    _ = depth*n := by simp

end AuxiliaryTree
namespace DataProducer
open AuxiliaryTree FactorController

/-- A failing producer only visits a prefix of the genuine occurrence tree.
Whenever it proceeds below a node, the validated factor list forces exactly the
canonical children. This bound does not assume that any stochastic test passed. -/
theorem build_requests_length (n : ℕ) (choose : Choices) (depth : ℕ) (path : List ℕ) (m : ℕ) :
    (build n choose depth path m).requests.length  ≤  (visits depth m).length := by
  induction depth generalizing path m with
  | zero => simp [build,Logged.abort,visits]
  | succ depth ih =>
    cases hs : (nodeRun n choose path m).result with
    | none =>
      simp only [build,Logged.bind,hs,visits,List.length_cons]
      change 1 ≤ _+1
      omega
    | some ps =>
      have hf := nodeRun_record hs
      simp only [build,Logged.bind,hs,Logged.map_requests,hf,recordChildren_factorization,
        List.length_append,visits,List.length_cons,List.length_flatMap]
      have ht := Logged.traverse_requests_length (fun d => build n choose depth (path++[d]) d) (children m)
      have hsum : ((children m).map (fun d => (build n choose depth (path++[d]) d).requests.length)).sum  ≤ 
          ((children m).map (fun d => (visits depth d).length)).sum := by
        exact list_map_sum_le _ _ _ (fun d _ => ih _ d)
      have ht' := ht.trans hsum
      change 1+_  ≤  _+1
      omega

lemma full_requests_length {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (choose : Choices) :
    (build n choose (2*n) [] m).requests.length  ≤  2*n^2 := by
  exact (build_requests_length n choose (2*n) [] m).trans
    (by simpa only [pow_two,Nat.mul_assoc] using visits_length_le hm hb (2*n))

/-- Count every local splitting request, including the final failed one. -/
noncomputable def splitRequests (n : ℕ) (choose : Choices) (depth : ℕ) (m : ℕ) : List (NodeKey×(ℕ×ℕ)) :=
  (build n choose depth [] m).requests.flatMap (fun k =>
    (queries (choose k) (2*n) 0 [k.2]).map (k,·))

lemma splitRequests_length {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (choose : Choices) :
    (splitRequests n choose (2*n) m).length  ≤  4*n^3 := by
  simp only [splitRequests,List.length_flatMap,List.length_map]
  calc
    _  ≤  ((build n choose (2*n) [] m).requests.map (fun _ => 2*n)).sum := by
      exact list_map_sum_le _ _ _ (fun k _ => queries_length _ _ _ _)
    _ = (build n choose (2*n) [] m).requests.length*(2*n) := by simp
    _  ≤  (2*n^2)*(2*n) := Nat.mul_le_mul_right _ (full_requests_length hm hb choose)
    _ = 4*n^3 := by ring

lemma padded_transition_bound {n : ℕ} (hn : 128 ≤ n) : 4*n^3*(n^5+1)<n^10 := by
  have hp : 1 ≤ n^5 := Nat.one_le_pow _ _ (by omega)
  have hsmall : 8<n^2 := by
    have hh := Nat.pow_le_pow_left hn 2
    norm_num at hh
    omega
  calc
    _  ≤  4*n^3*(2*n^5) := Nat.mul_le_mul_left _ (by omega)
    _ = 8*n^8 := by ring
    _ < n^2*n^8 := Nat.mul_lt_mul_of_pos_right hsmall (pow_pos (by omega) _)
    _ = n^10 := by ring

end DataProducer
end ExactQuantumFactoring


end

end OAI
