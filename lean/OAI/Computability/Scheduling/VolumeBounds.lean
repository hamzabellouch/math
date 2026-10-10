import OAI.Computability.Scheduling.Polynomial

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16

section
namespace ThreeMachine.StackCompiler
namespace Realizer
variable {α : Type u1} [Coding α]

theorem time_iterate_le {f : α → α} (R : Realizer f) (m : ℕ) (a : α) (T V : ℕ)
    (hT : ∀ j < m, R.time (f^[j] a) ≤ T)
    (hV : ∀ j ≤ m, volume (f^[j] a) ≤ V) :
    R.iterate.time (m,a) ≤ 10000*(m+1)*(T+V+m+1) := by
  exact Uniform.time_iterate_le (R.uniform Unit) () m a T V hT hV

theorem time_add_le (a b : ℕ) : add.time (a,b) ≤ 10000000*(a+b+1)^2 := by
  have h := time_iterate_le succ a b (200*(a+b+1)) (2*(a+b)+1)
    (fun j hj => by rw [iterate_succ]; exact (time_succ_le _).trans (by omega))
    (fun j hj => by rw [iterate_succ,volume_nat]; omega)
  change succ.iterate.time (a,b) ≤ _
  nlinarith

theorem time_sub_le (a b : ℕ) : sub.time (a,b) ≤ 10000000*(a+b+1)^2 := by
  have h := time_iterate_le pred b a (2*a+3) (2*a+1)
    (fun j _ => by rw [iterate_pred]; change volume (a-j)+2 ≤ _; rw [volume_nat]; omega)
    (fun j _ => by rw [iterate_pred,volume_nat]; omega)
  simp only [sub,time_congr,time_comp,swap,time_pair,time_fst,time_snd,volume_pair,volume_nat]
  nlinarith

theorem time_le_le (a b : ℕ) : le.time (a,b) ≤ 1000000000*(a+b+1)^2 := by
  have hs := time_sub_le a b
  have hp := time_test_le (fun n : ℕ => decide (0 < n)) (by intro n; cases n <;> rfl) (a-b)
  change positive.time (a-b) ≤ 10000*(volume (a-b)+1) at hp
  simp only [volume_nat] at hp
  have hn := time_not_le (decide (0 < a-b))
  have hv := volume_bool (decide (0 < a-b))
  simp only [le,time_congr,time_comp,isZero,volume_nat]
  have hsq : a+b+1 ≤ (a+b+1)^2 := le_self_pow (by omega) (by decide)
  omega

theorem time_eqNat_le (a b : ℕ) : eqNat.time (a,b) ≤ 10000000000*(a+b+1)^2 := by
  have hl := time_le_le a b
  have hr := time_le_le b a
  have ha := time_and_le (decide (a ≤ b),decide (b ≤ a))
  have hv := volume_bool (decide (a ≤ b))
  have hw := volume_bool (decide (b ≤ a))
  simp only [eqNat,time_congr,time_comp,time_pair,swap,time_fst,time_snd,volume_pair,volume_nat,
    Function.comp_apply]
  nlinarith

end Realizer
namespace Uniform
variable {I : Type u2} {α : I → Type u3} [∀ i, Coding (α i)]

theorem foldTime_length_le (i : I) (xs : List (α i)) (n : ℕ) :
    Realizer.foldTime ((snd.comp (Realizer.succ.uniform I) :
      Uniform (fun i (x : α i × ℕ) => x.2+1)).specialize i) n xs ≤
      1000*(xs.length+1)*(volume xs+n+xs.length+1) := by
  induction xs generalizing n with
  | nil => simp only [Realizer.foldTime,List.length_nil,volume_nil]; omega
  | cons a xs ih =>
    have hi := ih (n+1)
    have ht := Realizer.time_succ_le n
    rw [Realizer.foldTime]
    change (snd.comp (Realizer.succ.uniform I)).time i (a,n)+_+
      20*(volume (a::xs)+volume n+volume (n+1)+1) ≤ _
    simp only [time_comp,time_snd,time_uniform,volume_pair,volume_nat,volume_cons,List.length_cons,Function.comp_apply]
    nlinarith [volume_pos a,volume_pos xs]

theorem time_length_le (i : I) (xs : List (α i)) :
    length.time i xs ≤ 100000*(xs.length+1)*(volume xs+1) := by
  have hf := foldTime_length_le i xs 0
  have hv := length_le_volume xs
  simp only [length,time_congr,time_comp,time_pair,time_id,time_zero,time_fold,volume_pair,volume_nat]
  nlinarith [volume_pos xs]

theorem volume_drop_le {i : I} (xs : List (α i)) (n : ℕ) : volume (xs.drop n) ≤ volume xs :=
  volume_sublist (List.drop_sublist _ _)

theorem time_drop_le (i : I) (xs : List (α i)) (n : ℕ) :
    drop.time i (xs,n) ≤ 1000000*(n+1)*(volume xs+n+1) := by
  have he : ∀ j (ys : List (α i)), List.tail^[j] ys = ys.drop j := by
    intro j; induction j with
    | zero => intro ys; rfl
    | succ j ih => intro ys; rw [Function.iterate_succ_apply,ih,List.drop_tail]
  have h := time_iterate_le (tail : Uniform (fun i (xs : List (α i)) => xs.tail)) i n xs
    (volume xs+2) (volume xs)
    (fun j _ => by rw [he,time_tail]; exact Nat.add_le_add_right (volume_drop_le xs j) _)
    (fun j _ => by rw [he]; exact volume_drop_le xs j)
  simp only [drop,time_congr,time_comp,swap,time_pair,time_fst,time_snd,volume_pair,volume_nat]
  nlinarith [volume_pos xs]

theorem time_getElem?_le (i : I) (xs : List (α i)) (n : ℕ) :
    getElem?.time i (xs,n) ≤ 10000000*(n+1)*(volume xs+n+1) := by
  have hd := time_drop_le i xs n
  have hh := time_head?_le i (xs.drop n)
  have hv := volume_drop_le xs n
  simp only [getElem?,time_congr,time_comp]
  nlinarith [volume_pos xs]

end Uniform
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_prod {α : Type u4} {β : Type u5} [Coding α] [Coding β] (x : α × β) :
    volume x = volume x.1+volume x.2+1 := by cases x; exact volume_pair _ _

@[simp] theorem volume_state {n : ℕ} (x : Algorithm.State (Fin n)) :
    volume x = volume x.left+volume x.middle+volume x.right+2 := by
  change volume (x.left,(x.middle,x.right)) = _
  simp only [volume_pair]; omega

theorem volume_finRange_le (n : ℕ) : volume (List.finRange n) ≤ 3*(n+1)^2 := by
  have h := volume_list_le (List.finRange n) (2*n+1) (fun a _ => by rw [volume_fin]; have := a.isLt; omega)
  rw [List.length_finRange] at h
  nlinarith

theorem volume_universe_le {n : ℕ} (x : Universe n) : volume x ≤ 3*(n+1)^2 :=
  volume_finRange_le n

@[simp] theorem volume_cardinal {n : ℕ} (x : Cardinal n) : volume x = 2*n+1 := volume_nat n

theorem volume_bool_vector_le {n : ℕ} (v : Fin n → Bool) : volume v ≤ 4*n+1 := by
  have h := volume_function_le v 3 (fun _ => volume_bool _)
  omega

theorem volume_matrix_le {n : ℕ} (M : Matrix n) : volume M ≤ 10*(n+1)^2 := by
  have h := volume_function_le M (4*n+1) (fun _ => volume_bool_vector_le _)
  nlinarith

theorem volume_state_le {n : ℕ} (x : Algorithm.State (Fin n)) : volume x ≤ 12*(n+1)^2 := by
  have h₁ := volume_finset_le x.left
  have h₂ := volume_finset_le x.middle
  have h₃ := volume_finset_le x.right
  rw [volume_state]
  have hpos : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem volume_block_le {n : ℕ} (b : Algorithm.Block (Fin n)) (hl : b.length ≤ n)
    (ht : ∀ v, b.time v ≤ n) : volume b ≤ 10*(n+1)^2 := by
  have h := volume_function_le b.time (2*n+1) (by intro v; rw [volume_nat]; have := ht v; omega)
  change volume (b.length,b.time) ≤ _
  simp only [volume_pair,volume_nat]
  nlinarith

namespace Poly
variable {I : Type u6} {s n f : I → ℕ} {d : ℕ}

theorem precomp (h : Poly s f d) {J : Type u7} (g : J → I) : Poly (s ∘ g) (f ∘ g) d := Majorized.precomp h g

theorem volumeNat (h : Poly s f d) : Poly s (fun i => volume (f i)) d := by
  simp only [volume_nat]
  poly_bound

theorem volumeBool (s : I → ℕ) (b : I → Bool) : Poly s (fun i => volume (b i)) 0 :=
  of_le (fun i => volume_bool (b i)) (const s 3)

theorem volumeUnit (s : I → ℕ) (b : I → Unit) : Poly s (fun i => volume (b i)) 0 := by
  have h : (fun i => volume (b i)) = fun _ => 1 := by funext i; cases b i; rfl
  rw [h]; exact const s 1

theorem volumeFin (hn : Poly s n d) (v : ∀ i, Fin (n i)) : Poly s (fun i => volume (v i)) d := by
  apply of_le (g := fun i => 2*n i+1) (by intro i; rw [volume_fin]; have := (v i).isLt; omega)
  poly_bound

theorem volumeFinset (hn : Poly s n d) (v : ∀ i, Finset (Fin (n i))) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_finset_le (v i))
  poly_bound

theorem volumeUniverse (hn : Poly s n d) (v : ∀ i, Universe (n i)) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_universe_le (v i))
  poly_bound

theorem volumeCardinal (hn : Poly s n d) (v : ∀ i, Cardinal (n i)) :
    Poly s (fun i => volume (v i)) d := by
  simp only [volume_cardinal]
  poly_bound

theorem volumeBoolVector (hn : Poly s n d) (v : ∀ i, Fin (n i) → Bool) :
    Poly s (fun i => volume (v i)) d := by
  apply of_le (fun i => volume_bool_vector_le (v i))
  poly_bound

theorem volumeMatrix (hn : Poly s n d) (v : ∀ i, Matrix (n i)) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_matrix_le (v i))
  poly_bound

theorem volumeState (hn : Poly s n d) (v : ∀ i, Algorithm.State (Fin (n i))) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_state_le (v i))
  poly_bound

variable {α : I → Type u8} {β : I → Type u9} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem volumeProd (f : ∀ i, α i × β i) {d e : ℕ}
    (h₁ : Poly s (fun i => volume (f i).1) d) (h₂ : Poly s (fun i => volume (f i).2) e) :
    Poly s (fun i => volume (f i)) (Max.max d e) := by
  simp only [volume_prod]
  poly_bound

omit [∀ i, Coding (β i)] in
theorem volumeList {xs : ∀ i, List (α i)} {V : I → ℕ} {d e : ℕ}
    (hl : Poly s (fun i => (xs i).length) d) (hV : Poly s V e)
    (hv : ∀ i, ∀ a ∈ xs i, volume a ≤ V i) :
    Poly s (fun i => volume (xs i)) (d+e) := by
  apply of_le (fun i => volume_list_le (xs i) (V i) (hv i))
  poly_bound

end Poly
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_ofFn {α : Type u10} [Coding α] {n : ℕ} (f : Fin n → α) :
    volume (List.ofFn f) = volume f := rfl

@[simp] theorem volume_sort {n : ℕ} (s : Finset (Fin n)) : volume (s.sort (· ≤ ·)) = volume s := rfl

theorem volume_function_apply_le {α : Type u11} [Coding α] {n : ℕ} (f : Fin n → α) (v : Fin n) :
    volume (f v) ≤ volume f := volume_mem_le (List.mem_ofFn.mpr ⟨v,rfl⟩)

theorem nat_function_apply_le {n : ℕ} (f : Fin n → ℕ) (v : Fin n) : f v ≤ volume f := by
  have := volume_function_apply_le f v
  rw [volume_nat] at this
  omega

namespace Uniform
variable {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

@[simp] theorem time_functionListAny (d : I → ℕ) (i : I) (f : Fin (d i) → α i) :
    (functionListAny d).time i f = volume f+2 := rfl

@[simp] theorem time_finValue (d : I → ℕ) (i : I) (v : Fin (d i)) :
    (finValue d).time i v = volume v+2 := rfl

theorem time_functionGetOptionAny_le (d : I → ℕ) (i : I) (f : Fin (d i) → α i) (v : Fin (d i)) :
    (functionGetOptionAny d).time i (f,v) ≤ 100000000*(d i+1)*(volume f+d i+1) := by
  have ht := time_getElem?_le i (List.ofFn f) v.val
  have hv := v.isLt
  simp only [functionGetOptionAny,time_congr,time_comp,time_pair,time_fst,time_snd,
    time_functionListAny,time_finValue,volume_pair,volume_fin,volume_nat,volume_ofFn,
    Function.comp_apply] at ht ⊢
  nlinarith [volume_pos f]

theorem time_functionGetAny_eq (d : I → ℕ) (i : I) (f : Fin (d i) → α i) (v : Fin (d i)) :
    (functionGetAny d).time i (f,v) = (functionGetOptionAny d).time i (f,v)+11*volume (f v)+34 := by
  change (functionGetOptionAny d).time i (f,v)+
    ((functionGetOptionAny d).transform (enc (f,v))).size+2+
    10*(((functionGetOptionAny d).transform (enc (f,v))).size+1) = _
  rw [(functionGetOptionAny d).correct]
  change _+volume (Option.some (f v))+2+10*(volume (Option.some (f v))+1) = _
  rw [volume_some]
  omega

theorem time_functionGetAny_le (d : I → ℕ) (i : I) (f : Fin (d i) → α i) (v : Fin (d i)) :
    (functionGetAny d).time i (f,v) ≤ 1000000000*(d i+1)*(volume f+d i+1) := by
  rw [time_functionGetAny_eq]
  have h := time_functionGetOptionAny_le d i f v
  have hv := volume_function_apply_le f v
  nlinarith [volume_pos f]

theorem time_functionGet_le {α : ℕ → Type u15} [∀ n, Coding (α n)]
    (n : ℕ) (f : Fin n → α n) (v : Fin n) :
    functionGet.time n (f,v) ≤ 1000000000*(n+1)*(volume f+n+1) :=
  time_functionGetAny_le (fun n => n) n f v

@[simp] theorem time_reindex {f : ∀ i, α i → β i} (R : Uniform f) {J : Type u16}
    (φ : J → I) (j : J) (x : α (φ j)) : (R.reindex φ).time j x = R.time (φ j) x := rfl

end Uniform
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

end ThreeMachine.StackCompiler
end

end OAI
