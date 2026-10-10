import OAI.Computability.MatchingCount.RawSearch

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode

def PathSize (p : Paths) (M : ℕ) : Prop := ∀ q∈p,(encode q).length≤M

lemma initial_size (n a : ℕ) : PathSize (initial n a) (4*a+3) := by
  intro q hq
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  split_ifs
  · simp only [code_option_some,code_cons,code_nat_length,code_nil,List.length_nil,pairBits_length]
    omega
  · simp only [code_option_none,List.length_nil]; omega

lemma pathStep_size (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) (M : ℕ)
    (hp : PathSize p M) : PathSize (pathStep n c b p) (M+4*n+2) := by
  intro q hq
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  have hvn := List.mem_range.mp hv
  have hsize (u : ℕ) : (encode (nth p u)).length≤M :=
    nth_code_bound p u M (Nat.zero_le M) hp
  change (encode (match nth p v with
    | some l => some l
    | none => match predecessor n c b p v with
      | none => none
      | some u => (nth p u).map (fun l => v::l))).length≤_
  cases h : nth p v with
  | some l => dsimp only; have hh := hsize v; rw [h] at hh; omega
  | none =>
    cases hu : predecessor n c b p v with
    | none => simp only [code_option_none,List.length_nil]; omega
    | some u =>
      dsimp only
      have hh := option_prepend_bound v (nth p u)
      have he := hsize u
      omega

lemma search_size (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    PathSize (search n c b a k) (4*a+3+k*(4*n+2)) := by
  induction k with
  | zero => simpa only [search,Function.iterate_zero,id_eq,Nat.zero_mul,Nat.add_zero] using initial_size n a
  | succ k ih =>
    have hh := pathStep_size n c b _ _ ih
    simpa only [search,Function.iterate_succ_apply',Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hh

lemma search_length (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    (search n c b a k).length=n := by
  cases k with
  | zero => simp [search,initial,tab]
  | succ k => simp [search,Function.iterate_succ_apply',pathStep,tab]

lemma search_code_bound (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) :
    (encode (search n c b a k)).length≤n*(2*(4*a+3+k*(4*n+2))+1) := by
  have h := list_code_bound _ _ (search_size n c b a k)
  rwa [search_length] at h

end BinaryMatching.Raw
end

end OAI
