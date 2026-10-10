import OAI.Computability.MatchingCount.RawPrimitives

namespace OAI

section

namespace BinaryMatching.StackCode
open BinaryMatching.Raw

@[simp] lemma code_bool_length (b : Bool) : (encode b).length=1 := rfl
@[simp] lemma code_nat_length (n : ℕ) : (encode n).length=n := unary_length n
@[simp] lemma code_int_length (z : ℤ) : (encode z).length=z.natAbs+3 := by
  simp only [encode_int,encode_prod,pairBits_length,intParts,code_bool_length,code_nat_length]
  omega
@[simp] lemma code_pair_length {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z).length=2*(encode z.1).length+(encode z.2).length+1 := pairBits_length _ _

lemma pair_left_le {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z.1).length≤(encode z).length := by simp only [code_pair_length]; omega
lemma pair_right_le {α β : Type} [Coding α] [Coding β] (z : α×β) :
    (encode z.2).length≤(encode z).length := by simp only [code_pair_length]; omega

lemma nth_code_bound {α : Type} [Coding α] [Inhabited α] (l : List α) (i M : ℕ)
    (hd : (encode (default:α)).length≤M) (h : ∀ a∈l,(encode a).length≤M) :
    (encode (nth l i)).length≤M := by
  unfold nth
  cases hi : l[i]? with
  | none => exact hd
  | some a =>
    exact h a (List.mem_of_getElem? hi)

lemma nth_code_le {α : Type} [Coding α] [Inhabited α] (l : List α) (i : ℕ) :
    (encode (nth l i)).length≤(encode l).length+(encode (default:α)).length := by
  apply nth_code_bound
  · omega
  · intro a ha
    have hh := element_code_le l a ha
    omega

lemma tab_code_bound {α : Type} [Coding α] (n M : ℕ) (f : ℕ → α)
    (h : ∀ i,i<n → (encode (f i)).length≤M) :
    (encode (tab n f)).length≤n*(2*M+1) := by
  have hh := list_code_bound (tab n f) M (by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact h _ (List.mem_range.mp hi))
  simpa only [tab,List.length_map,List.length_range] using hh

lemma matrix_code_bound {α : Type} [Coding α] (n M : ℕ) (f : ℕ → ℕ → α)
    (h : ∀ i,i<n → ∀ j,j<n → (encode (f i j)).length≤M) :
    (encode (matrix n f)).length≤n*(2*(n*(2*M+1))+1) := by
  apply tab_code_bound
  intro i hi
  exact tab_code_bound _ _ _ (h i hi)

lemma cut_code_length (S : Cut) : (encode S).length=3*S.length := by
  induction S with
  | nil => rfl
  | cons b S ih => simp only [code_cons,pairBits_length,code_bool_length,ih,List.length_cons]; omega

lemma option_prepend_bound (v : ℕ) (p : Option (List ℕ)) :
    (encode (p.map (v::·))).length≤(encode p).length+4*v+2 := by
  cases p with
  | none => simp only [Option.map_none,code_option_none,List.length_nil]; omega
  | some l => simp only [Option.map_some,code_option_some,code_cons,pairBits_length,code_nat_length]; omega

end BinaryMatching.StackCode
end

end OAI
