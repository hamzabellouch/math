import OAI.Computability.MatchingCount.RawFlow

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode

lemma nth_property {α : Type} [Inhabited α] (P : α → Prop) (l : List α) (i : ℕ)
    (hd : P default) (h : ∀ a∈l,P a) : P (nth l i) := by
  unfold nth
  cases hi : l[i]? with
  | none => exact hd
  | some a => exact h a (List.mem_of_getElem? hi)

def MatrixBound (b : Matrix ℤ) (M : ℕ) : Prop := ∀ row∈b,∀ v∈row,v.natAbs≤M

def Square {α : Type} (n : ℕ) (b : Matrix α) : Prop := b.length=n ∧ ∀ row∈b,row.length=n

lemma matrix_square {α : Type} (n : ℕ) (f : ℕ → ℕ → α) : Square n (matrix n f) := by
  constructor
  · simp [matrix,tab]
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simp [tab]

lemma matrix_bound (n M : ℕ) (f : ℕ → ℕ → ℤ) (h : ∀ i,i<n → ∀ j,j<n → (f i j).natAbs≤M) :
    MatrixBound (matrix n f) M := by
  intro row hr v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
  exact h _ (List.mem_range.mp hi) _ (List.mem_range.mp hj)

lemma get_abs_bound (b : Matrix ℤ) (M : ℕ) (hb : MatrixBound b M) (i j : ℕ) :
    (get b i j).natAbs≤M := by
  apply nth_property (fun z : ℤ => z.natAbs≤M)
  · exact Nat.zero_le _
  · apply nth_property (fun row : List ℤ => ∀ v∈row,v.natAbs≤M)
    · intro v hv; cases hv
    · exact hb

lemma matrix_bound_code (n M : ℕ) (b : Matrix ℤ) (hs : Square n b) (hb : MatrixBound b M) :
    (encode b).length≤n*(2*(n*(2*(M+3)+1))+1) := by
  have hh := list_code_bound b (n*(2*(M+3)+1)) (by
    intro row hr
    have hrow := list_code_bound row (M+3) (by
      intro v hv
      rw [code_int_length]
      have he := hb row hr v hv
      omega)
    rwa [hs.2 row hr] at hrow)
  rwa [hs.1] at hh

lemma pathFlow_abs (p : List ℕ) (i j : ℕ) : (pathFlow p i j).natAbs≤p.length := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton a => simp [pathFlow]
  | cons_cons v u p _ ih =>
    have hip := ih u
    have he : pathFlow (v::u::p) i j=
        ((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0))+
        pathFlow (u::p) i j := by
      simp [pathFlow]
    rw [he]
    have hsmall : (((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0)):ℤ).natAbs≤1 := by
      split_ifs <;> decide
    have h := Int.natAbs_add_le
      (((if i=u ∧ j=v then 1 else 0)-(if i=v ∧ j=u then 1 else 0)):ℤ) (pathFlow (u::p) i j)
    simp only [List.length_cons] at *
    omega

lemma search_path_bound (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a z : ℕ) (p : List ℕ)
    (hp : nth (search n c b a n) z=some p) : p.length≤4*a+3+n*(4*n+2) := by
  have hh := nth_code_bound (search n c b a n) z (4*a+3+n*(4*n+2))
    (Nat.zero_le _) (search_size n c b a n)
  rw [hp,code_option_some] at hh
  have hl := list_length_le_code p
  omega

lemma augment_bound (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ) (M : ℕ)
    (hb : MatrixBound b M) : MatrixBound (augment n c a z b) (M+(4*a+3+n*(4*n+2))) := by
  unfold augment
  cases hp : nth (search n c b a n) z with
  | none => intro row hr v hv; have := hb row hr v hv; omega
  | some p =>
    apply matrix_bound
    intro i hi j hj
    have hh := Int.natAbs_add_le (get b i j) (pathFlow p i j)
    have h₁ := get_abs_bound b M hb i j
    have h₂ := (pathFlow_abs p i j).trans (search_path_bound n c b a z p hp)
    omega

lemma augment_square (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ)
    (hb : Square n b) : Square n (augment n c a z b) := by
  unfold augment
  split
  · exact hb
  · exact matrix_square _ _

lemma flow_bound (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) :
    MatrixBound (flow n c a z k) (k*(4*a+3+n*(4*n+2))) := by
  induction k with
  | zero => simpa only [flow,Function.iterate_zero,Function.id_def,Nat.zero_mul] using matrix_bound n 0 (fun _ _ => 0) (fun _ _ _ _ => le_rfl)
  | succ k ih =>
    have hh := augment_bound n c a z _ _ ih
    simpa only [flow,Function.iterate_succ_apply',Nat.add_mul,Nat.one_mul] using hh

lemma flow_square (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) : Square n (flow n c a z k) := by
  induction k with
  | zero => exact matrix_square _ _
  | succ k ih => simpa only [flow,Function.iterate_succ_apply'] using augment_square n c a z _ ih
lemma flow_code_bound (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) :
    (encode (flow n c a z k)).length≤n*(2*(n*(2*(k*(4*a+3+n*(4*n+2))+3)+1))+1) :=
  matrix_bound_code _ _ _ (flow_square n c a z k) (flow_bound n c a z k)
end BinaryMatching.Raw
end

end OAI
