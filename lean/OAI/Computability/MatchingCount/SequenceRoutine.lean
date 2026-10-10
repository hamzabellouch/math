import OAI.Computability.MatchingCount.MapRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_take_le {α : Type} [Coding α] (l : List α) (n : ℕ) :
    (encode (l.take n)).length≤(encode l).length := by
  have h := congrArg (fun xs => (encode xs).length) (List.take_append_drop n l)
  rw [code_append,List.length_append] at h
  omega

lemma code_replicate {α : Type} [Coding α] (a : α) (n : ℕ) :
    (encode (List.replicate n a)).length=n*(2*(encode a).length+1) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,code_cons,pairBits_length,ih]; nlinarith

def dupStep {α : Type} (z : α×List α) : α×List α := (z.1,z.1::z.2)
lemma dupStep_iterate {α : Type} (n : ℕ) (z : α×List α) :
    dupStep^[n] z=(z.1,List.replicate n z.1++z.2) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,dupStep,List.replicate_succ]

lemma code_zip_bound {α β : Type} [Coding α] [Coding β] (l : List α) (m : List β) :
    (encode (l.zip m)).length≤2*(encode l).length+(encode m).length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      have h := ih m
      simp only [List.zip_cons_cons,code_cons,encode_prod,pairBits_length]
      omega

def zipStep {α β : Type} [Inhabited α] [Inhabited β]
    (z : List α×(List β×List (α×β))) : List α×(List β×List (α×β)) :=
  (z.1.tail,z.2.1.tail,if z.1.isEmpty || z.2.1.isEmpty then z.2.2
    else z.2.2++[(z.1.headD default,z.2.1.headD default)])

lemma zipStep_iterate {α β : Type} [Inhabited α] [Inhabited β]
    (n : ℕ) (z : List α×(List β×List (α×β))) :
    zipStep^[n] z=(z.1.drop n,z.2.1.drop n,
      z.2.2++(z.1.take n).zip (z.2.1.take n)) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rcases z with ⟨l,m,o⟩
    cases l <;> cases m <;>
      simp [Function.iterate_succ_apply,zipStep,ih,List.append_assoc]

lemma zip_take_right_of_ge {α β : Type} (l : List α) (m : List β) (n : ℕ)
    (hn : l.length≤n) : l.zip (m.take n)=l.zip m := by
  induction l generalizing m n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      cases m with
      | nil => simp
      | cons b m => simp only [List.take_succ_cons,List.zip_cons_cons,ih m n (by simpa using hn)]

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem listReplicate : Poly (fun z : ℕ×α => List.replicate z.1 z.2) := by
  have hs : Poly (dupStep : α×List α → α×List α) := by unfold dupStep; fun_prop
  have hi : Poly (fun z : ℕ×(α×List α) => dupStep^[z.1] z.2) :=
    boundedIterate dupStep hs ((X+1)^2) (by
      intro z j hj
      rw [dupStep_iterate]
      simp only [encode_prod,pairBits_length,code_append,List.length_append,code_replicate,
        encode_nat,unary_length,eval_pow,eval_add,eval_X,eval_one]
      have hm := Nat.mul_le_mul_right (2*(encode z.2.1).length+1) hj
      nlinarith)
  have h : Poly (fun z : ℕ×α => (dupStep^[z.1] (z.2,[])).2) :=
    second _ (comp _ (fun z : ℕ×α => (z.1,(z.2,[]))) hi (by fun_prop))
  exact h.congr (fun z => by simp [dupStep_iterate])

@[fun_prop] theorem listZip [Inhabited α] [Inhabited β] :
    Poly (fun z : List α×List β => z.1.zip z.2) := by
  have hs : Poly (zipStep : List α×(List β×List (α×β)) → _) := by unfold zipStep; fun_prop
  have hi : Poly (fun z : ℕ×(List α×(List β×List (α×β))) => zipStep^[z.1] z.2) :=
    boundedIterate zipStep hs (2*X) (by
      intro z j hj
      rw [zipStep_iterate]
      have h₁ := code_drop_le z.2.1 j
      have h₂ := code_drop_le z.2.2.1 j
      have h₃ := code_take_le z.2.1 j
      have h₄ := code_take_le z.2.2.1 j
      have h₅ := code_zip_bound (z.2.1.take j) (z.2.2.1.take j)
      simp only [encode_prod,pairBits_length,code_append,List.length_append,encode_nat,unary_length,
        eval_mul,eval_ofNat,eval_X]
      omega)
  have h : Poly (fun z : List α×List β => (zipStep^[(encode z.1).length] (z.1,z.2,[])).2.2) := by
    apply second
    apply second
    apply comp _ (fun z : List α×List β => ((encode z.1).length,(z.1,z.2,[]))) hi
    apply pair
    · exact comp _ Prod.fst codeLength (first _ identity)
    · fun_prop
  exact h.congr (fun z => by
    rw [zipStep_iterate]
    simp only [List.nil_append,List.take_of_length_le (list_length_le_code z.1)]
    exact zip_take_right_of_ge z.1 z.2 _ (list_length_le_code z.1))

@[fun_prop] theorem listMapParam [Inhabited α] [Inhabited γ]
    (f : γ×α → β) (hf : Poly f) : Poly (fun z : γ×List α => z.2.map (fun a => f (z.1,a))) := by
  have hm : Poly (List.map f) := listMap f hf
  have h : Poly (fun z : γ×List α => (List.zip (List.replicate z.2.length z.1) z.2).map f) := by fun_prop
  exact h.congr (fun z => by
    have hz : List.zip (List.replicate z.2.length z.1) z.2=z.2.map (fun a => (z.1,a)) := by
      induction z.2 with
      | nil => rfl
      | cons a l ih => simpa only [List.length_cons,List.replicate_succ,List.zip_cons_cons,List.map_cons] using congrArg (List.cons (z.1,a)) ih
    simp [hz,List.map_map,Function.comp_def])

end Poly
end BinaryMatching.StackCode
end

end OAI
