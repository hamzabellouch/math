import Mathlib

namespace OAI

section
namespace SharpLogRamsey.TreeShapes
open BinaryTree Finset
open scoped Classical

def bits : BinaryTree Unit→List Bool
  | .nil => [false]
  | .node _ l r => true::(bits l++bits r)

lemma bits_length (t : BinaryTree Unit) : (bits t).length=2*t.numNodes+1 := by
  induction t with
  | nil => simp [bits]
  | node _ l r hl hr => simp only [bits,List.length_cons,List.length_append,numNodes,hl,hr]; omega

lemma prefix_free (t t' : BinaryTree Unit) (u v : List Bool)
    (h : bits t++u=bits t'++v) : t=t' ∧ u=v := by
  induction t generalizing t' u v with
  | nil =>
    cases t' with
    | nil => simpa [bits] using h
    | node _ _ _ => simp [bits] at h
  | node a l r hl hr =>
    cases t' with
    | nil => simp [bits] at h
    | node a' l' r' =>
      have he : bits l++(bits r++u)=bits l'++(bits r'++v) := by
        simpa only [bits,List.cons_append,List.cons.injEq,true_and,List.append_assoc] using h
      obtain ⟨hl',hh⟩ := hl l' (bits r++u) (bits r'++v) he
      obtain ⟨hr',hu⟩ := hr r' u v hh
      exact ⟨by cases a;cases a';simp [hl',hr'],hu⟩

noncomputable def boundedEncode (N : ℕ) (S : Finset (BinaryTree Unit))
    (hS : ∀ t∈S,t.numNodes≤N) (t : S) : List.Vector Bool (2*N+1) :=
  ⟨bits t.val++List.replicate (2*N+1-(bits t.val).length) false,by
    have ht := hS t.val t.property
    simp only [List.length_append,List.length_replicate,bits_length]
    omega⟩

lemma boundedEncode_injective (N : ℕ) (S : Finset (BinaryTree Unit))
    (hS : ∀ t∈S,t.numNodes≤N) : Function.Injective (boundedEncode N S hS) := by
  intro s t he
  have hh := congrArg Subtype.val he
  exact Subtype.ext (prefix_free s.val t.val _ _ hh).1

theorem card_le (N : ℕ) (S : Finset (BinaryTree Unit))
    (hS : ∀ t∈S,t.numNodes≤N) : S.card≤2^(2*N+1) := by
  have h := Fintype.card_le_of_injective _ (boundedEncode_injective N S hS)
  simpa only [Fintype.card_coe,card_vector,Fintype.card_bool] using h

end SharpLogRamsey.TreeShapes

end

end OAI
