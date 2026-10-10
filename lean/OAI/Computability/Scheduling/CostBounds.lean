import OAI.Computability.Scheduling.ScheduleRoutines

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38 u39 u40

section

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_unit : volume () = 1 := rfl
@[simp] theorem volume_bool_false : volume Bool.false = 1 := rfl
@[simp] theorem volume_bool_true : volume Bool.true = 3 := rfl
@[simp] theorem volume_none {α : Type u1} [Coding α] : volume (none : Option α) = 1 := rfl
@[simp] theorem volume_some {α : Type u2} [Coding α] (a : α) : volume (some a) = volume a+2 := by
  simp only [volume,enc_some,Data.size_pair,Data.size_nil]

theorem volume_bool (b : Bool) : volume b ≤ 3 := by cases b <;> decide

theorem volume_list {α : Type u3} [Coding α] (xs : List α) :
    volume xs = 1+xs.length+(xs.map volume).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [volume_cons,List.length_cons,List.map_cons,List.sum_cons,ih]; omega

theorem volume_mem_le {α : Type u4} [Coding α] {xs : List α} {a : α}
    (ha : a ∈ xs) : volume a ≤ volume xs := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [volume_cons]; omega
    · have := ih ha; simp only [volume_cons]; omega

theorem volume_sublist {α : Type u5} [Coding α] {as bs : List α} (h : as.Sublist bs) :
    volume as ≤ volume bs := by
  induction h with
  | slnil => rfl
  | @cons a as bs h ih => simp only [volume_cons]; omega
  | @cons_cons a as bs h ih => simp only [volume_cons]; omega

theorem volume_filter_le {α : Type u6} [Coding α] (p : α → Bool) (xs : List α) :
    volume (xs.filter p) ≤ volume xs := volume_sublist (List.filter_sublist)

theorem volume_option_le {α : Type u7} [Coding α] (o : Option α) (V : ℕ)
    (hV : ∀ a ∈ o, volume a ≤ V) : volume o ≤ V+2 := by
  cases o with
  | none => simp only [volume_none]; omega
  | some a => simpa only [volume_some,Nat.add_le_add_iff_right] using hV a rfl

theorem volume_optionToList {α : Type u8} [Coding α] (o : Option α) :
    volume o.toList = volume o := by cases o <;> rfl

theorem volume_finset_le {n : ℕ} (s : Finset (Fin n)) : volume s ≤ 3*(n+1)^2 := by
  change volume (s.sort (· ≤ ·)) ≤ _
  have h := volume_list_le (s.sort (· ≤ ·)) (2*n+1) (fun a _ => by
    rw [volume_fin]; have := a.isLt; omega)
  have hh := Finset.card_le_univ s
  rw [Finset.length_sort] at h
  simp only [Fintype.card_fin] at hh
  nlinarith

theorem volume_function_le {α : Type u9} [Coding α] {n : ℕ} (f : Fin n → α) (V : ℕ)
    (h : ∀ v, volume (f v) ≤ V) : volume f ≤ 1+n*(V+1) := by
  change volume (List.ofFn f) ≤ _
  have hv := volume_list_le (List.ofFn f) V (by
    intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact h i)
  simpa only [List.length_ofFn,Nat.add_comm] using hv

namespace Realizer
variable {α : Type u10} {β : Type u11} [Coding α] [Coding β] {f : α × β → β}

theorem foldTime_le (R : Realizer f) (xs : List α) (P : β → Prop) (T V : ℕ)
    (hvol : ∀ b, P b → volume b ≤ V)
    (hstep : ∀ a ∈ xs, ∀ b, P b → P (f (a,b)))
    (htime : ∀ a ∈ xs, ∀ b, P b → R.time (a,b) ≤ T)
    (b : β) (hb : P b) :
    foldTime R b xs ≤ xs.length*(T+20*(volume xs+2*V+1))+1 := by
  induction xs generalizing b with
  | nil => simp only [foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have ha : a ∈ a :: xs := by simp
    have hs := hstep a ha b hb
    have hi := ih (fun a ha => hstep a (by simp [ha]))
      (fun a ha => htime a (by simp [ha])) (f (a,b)) hs
    have ht := htime a ha b hb
    have hv := hvol b hb
    have hw := hvol _ hs
    simp only [foldTime,volume_cons,List.length_cons] at hi ⊢
    nlinarith [volume_pos a,volume_pos xs]

end Realizer

namespace Uniform
variable {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
variable {f : ∀ i, α i × β i → β i}

theorem time_fold_le (R : Uniform f) (i : I) (xs : List (α i))
    (P : β i → Prop) (T V : ℕ) (hvol : ∀ b, P b → volume b ≤ V)
    (hstep : ∀ a ∈ xs, ∀ b, P b → P (f i (a,b)))
    (htime : ∀ a ∈ xs, ∀ b, P b → R.time i (a,b) ≤ T)
    (b : β i) (hb : P b) :
    R.fold.time i (xs,b) ≤ 50*(xs.length+1)*(T+volume xs+V+1) := by
  have h := Realizer.foldTime_le (R.specialize i) xs P T V hvol hstep htime b hb
  rw [time_fold]
  simp only [volume_pair]
  have hv := hvol b hb
  nlinarith [volume_pos xs]

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Realizer

theorem time_not_le (b : Bool) : not.time b ≤ 10000 := by cases b <;> decide

theorem time_and_le (x : Bool × Bool) : and.time x ≤ 10000 := by
  rcases x with ⟨a,b⟩; cases a <;> cases b <;> decide

theorem time_or_le (x : Bool × Bool) : or.time x ≤ 10000 := by
  rcases x with ⟨a,b⟩; cases a <;> cases b <;> decide

theorem time_succ_le (n : ℕ) : succ.time n ≤ 200*(n+1) := by
  have hu : (unit : Realizer (fun (_ : ℕ) => ())).time n = 2 := rfl
  simp only [succ,time_congr,time_comp,time_pair,time_id,hu,id_eq]
  simp only [volume_pair,volume_unit,volume_nat]
  change 2+(2*n+1+2)+20*((2*n+1)+1+(2*n+1)+1)+(volume ((),n)+2)+10*(1+(2*n+1)+1+1) ≤ _
  simp only [volume_pair,volume_unit,volume_nat]
  omega

theorem time_test_le {α : Type u15} [Coding α] (p : α → Bool)
    (h : ∀ x, (enc x).nonempty = p x) (x : α) :
    (test p h).time x ≤ 10000*(volume x+1) := by
  simp only [time,test,Routine.comp,Routine.pair,Routine.identity,Routine.nil,
    Routine.choose,Routine.constant,Data.size_pair,Data.size_nil]
  change (enc x).size+2+2+20*((enc x).size+(enc x).size+1+1)+
    (7*(20*((enc x).size+1+1)+50*3+50)+2+30*((enc x).size+1+1+3+1+1))+
    10*((enc x).size+1+1+1) ≤ _
  change _ ≤ 10000*((enc x).size+1)
  omega

end Realizer

namespace Uniform
variable {I : Type u16} {α : I → Type u17} {β : I → Type u18}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)]

@[simp] theorem time_uniform {δ : Type u19} {ε : Type u20} [Coding δ] [Coding ε]
    {f : δ → ε} (R : Realizer f) (i : I) (x : δ) : (R.uniform I).time i x = R.time x := rfl

theorem time_test_le (p : ∀ i, α i → Bool) (h : ∀ i x, (enc x).nonempty = p i x)
    (i : I) (x : α i) : (test p h).time i x ≤ 10000*(volume x+1) :=
  Realizer.time_test_le (p i) (h i) x

theorem time_head?_le (i : I) (xs : List (α i)) : head?.time i xs ≤ 10000*(volume xs+1) := by
  cases xs with
  | nil =>
    simp only [time,head?,Routine.comp,Routine.pair,Routine.identity,Routine.nil,
      Routine.choose,Routine.select,enc_nil,id_eq,Function.comp_apply,
      ite_true,Data.head,Data.size_pair,Data.size_nil,volume,enc_nil]
    omega
  | cons a xs =>
    dsimp only [time,head?,Routine.comp,Routine.pair,Routine.identity,Routine.nil,
      Routine.choose,Routine.select,Function.comp_apply,enc_cons,Data.head,Data.tail,
      Data.size_pair,Data.size_nil,Data.nonempty,id_eq,ite_true]
    simp only [ite_true,Data.size_pair,Data.size_nil,volume,enc_cons,Data.size_pair]
    omega

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

def Majorized {I : Type u21} (f g : I → ℕ) : Prop := ∃ C : ℕ, ∀ i, f i ≤ C*g i

namespace Majorized
variable {I : Type u22} {J : Type u23} {f g h s t : I → ℕ}

theorem refl (f : I → ℕ) : Majorized f f := ⟨1,fun _ => by omega⟩
theorem of_le (h : ∀ i, f i ≤ g i) : Majorized f g := ⟨1,fun i => by simpa using h i⟩
theorem trans (hf : Majorized f g) (hg : Majorized g h) : Majorized f h := by
  obtain ⟨C,hC⟩ := hf; obtain ⟨D,hD⟩ := hg
  exact ⟨C*D,fun i => (hC i).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left C (hD i))⟩
theorem mono (hf : Majorized f g) (h : ∀ i, g i ≤ s i) : Majorized f s :=
  hf.trans (of_le h)
theorem precomp (hf : Majorized f g) (a : J → I) : Majorized (f ∘ a) (g ∘ a) := by
  obtain ⟨C,hC⟩ := hf; exact ⟨C,fun i => hC (a i)⟩
theorem add (hf : Majorized f s) (hg : Majorized g s) : Majorized (fun i => f i+g i) s := by
  obtain ⟨C,hC⟩ := hf; obtain ⟨D,hD⟩ := hg
  refine ⟨C+D,fun i => ?_⟩
  simpa only [Nat.add_mul] using Nat.add_le_add (hC i) (hD i)
theorem mul (hf : Majorized f s) (hg : Majorized g t) :
    Majorized (fun i => f i*g i) (fun i => s i*t i) := by
  obtain ⟨C,hC⟩ := hf; obtain ⟨D,hD⟩ := hg
  refine ⟨C*D,fun i => ?_⟩
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul (hC i) (hD i)
theorem const (C : ℕ) (hs : ∀ i, 1 ≤ s i) : Majorized (fun _ => C) s := by
  exact ⟨C,fun i => by simpa using Nat.mul_le_mul_left C (hs i)⟩
theorem zero (s : I → ℕ) : Majorized (fun _ => 0) s := ⟨0,fun _ => by simp⟩
theorem const_mul (C : ℕ) (hf : Majorized f s) : Majorized (fun i => C*f i) s := by
  obtain ⟨D,hD⟩ := hf
  exact ⟨C*D,fun i => by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left C (hD i)⟩
theorem mul_const (hf : Majorized f s) (C : ℕ) : Majorized (fun i => f i*C) s := by
  simpa only [Nat.mul_comm] using hf.const_mul C

theorem pow (hf : Majorized f s) (d : ℕ) : Majorized (fun i => (f i)^d) (fun i => (s i)^d) := by
  obtain ⟨C,hC⟩ := hf
  refine ⟨C^d,fun i => ?_⟩
  simpa only [Nat.mul_pow] using Nat.pow_le_pow_left (hC i) d

theorem pow_mono (hs : ∀ i, 1 ≤ s i) {d e : ℕ} (hde : d ≤ e) :
    Majorized (fun i => (s i)^d) (fun i => (s i)^e) :=
  of_le (fun i => Nat.pow_le_pow_right (hs i) hde)

theorem sum (as : List J) {F : J → I → ℕ}
    (hF : ∀ a ∈ as, Majorized (F a) s) :
    Majorized (fun i => (as.map (fun a => F a i)).sum) s := by
  induction as with
  | nil => exact zero s
  | cons a as ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (hF a (by simp)).add (ih (fun a ha => hF a (by simp [ha])))

end Majorized
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_flatten {α : Type u24} [Coding α] (xs : List (List α)) :
    volume xs = volume xs.flatten+2*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have h := volume_append a xs.flatten
    simp only [volume_cons,List.flatten_cons,List.length_cons] at ih ⊢
    omega

namespace Uniform
variable {I : Type u25} {α : I → Type u26} {β : I → Type u27} {γ : I → Type u28}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

@[simp] theorem time_tail (i : I) (xs : List (α i)) : tail.time i xs = volume xs+2 := rfl
@[simp] theorem time_none (i : I) (x : α i) : (none : Uniform (fun i (_ : α i) => (Option.none : Option (β i)))).time i x = 2 := rfl

theorem time_some_le (i : I) (x : α i) : some.time i x ≤ 100*(volume x+1) := by
  change volume x+2+2+20*(volume x+volume x+1+1) ≤ _
  omega

theorem time_ite_le {p : ∀ i, α i → Bool} {f g : ∀ i, α i → β i}
    (P : Uniform p) (R : Uniform f) (S : Uniform g) (i : I) (x : α i) :
    (P.ite R S).time i x ≤ P.time i x+R.time i x+S.time i x+
      1000*(volume x+volume (f i x)+volume (g i x)+1) := by
  have hp := volume_bool (p i x)
  simp only [ite,time_congr,time_comp,time_pair,time_id,time_choose,time_snd,volume_pair]
  omega

theorem foldTime_cons (i : I) (xs ys : List (α i)) :
    Realizer.foldTime ((cons : Uniform (fun i (x : α i × List (α i)) => x.1 :: x.2)).specialize i) ys xs ≤
      100*xs.length*(volume xs+volume ys+1)+1 := by
  induction xs generalizing ys with
  | nil => simp only [Realizer.foldTime,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have hh := ih (a :: ys)
    change volume (a,ys)+2+Realizer.foldTime _ (a :: ys) xs+
      20*(volume (a :: xs)+volume ys+volume (a :: ys)+1) ≤ _
    simp only [volume_pair,volume_cons,List.length_cons] at hh ⊢
    nlinarith [volume_pos a,volume_pos xs,volume_pos ys]

theorem time_consFold (i : I) (xs ys : List (α i)) :
    cons.fold.time i (xs,ys) ≤ 200*(xs.length+1)*(volume xs+volume ys+1) := by
  have h := foldTime_cons i xs ys
  rw [time_fold]
  simp only [volume_pair]
  nlinarith

theorem foldTime_flatten (i : I) (xs : List (List (α i))) (ys : List (α i)) :
    Realizer.foldTime ((cons.fold : Uniform (fun i (x : List (α i) × List (α i)) =>
      x.1.foldl (fun b a => a :: b) x.2)).specialize i) ys xs ≤
      1000*(xs.length+xs.flatten.length)*(volume xs+volume ys+1)+1 := by
  induction xs generalizing ys with
  | nil => simp only [Realizer.foldTime,List.length_nil,List.flatten_nil,Nat.zero_add,Nat.mul_zero,Nat.zero_mul]; rfl
  | cons a xs ih =>
    have hh := ih (a.reverse ++ ys)
    have ht := time_consFold i a ys
    have hv := volume_append a.reverse ys
    rw [volume_reverse] at hv
    simp only [Realizer.foldTime,Realizer.fold_cons_eq]
    change cons.fold.time i (a,ys)+Realizer.foldTime _ (a.reverse ++ ys) xs+
      20*(volume (a :: xs)+volume ys+volume (a.reverse ++ ys)+1) ≤ _
    simp only [volume_cons,List.length_cons,List.flatten_cons,List.length_append] at hh ht ⊢
    nlinarith [volume_pos a,volume_pos xs,volume_pos ys]

theorem time_flatten (i : I) (xs : List (List (α i))) :
    flatten.time i xs ≤ 10000*(xs.length+xs.flatten.length+1)*(volume xs+1) := by
  have hf := foldTime_flatten i xs []
  have hr := time_reverse i xs.flatten.reverse
  simp only [volume_nil,List.length_reverse,volume_reverse] at hf hr
  have hv : volume xs.flatten ≤ volume xs := by rw [volume_flatten]; omega
  simp only [flatten,time_congr,time_comp,time_pair,time_id,time_nil,time_fold,
    Function.comp_apply,flatten_fold_eq,List.append_nil,volume_pair,volume_nil,volume_reverse]
  nlinarith [volume_pos xs,volume_pos xs.flatten]

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u29} {α : I → Type u30} {β : I → Type u31} {γ : I → Type u32}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_filterBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (a : α i) (e : γ i) (ys : List (α i)) :
    (filterBody P).time i (a,(e,ys)) ≤ P.time i (a,e)+
      10000*(volume a+volume e+volume ys+1) := by
  have ht := time_ite_le ((fst.pair (snd.comp fst)).comp P)
    ((fst.pair (snd.comp snd)).comp cons) (snd.comp snd) i (a,(e,ys))
  simp only [time_comp,time_pair,time_fst,time_snd,time_cons,volume_pair,volume_cons,Function.comp_apply] at ht
  simp only [filterBody,time_pair,time_comp,time_snd,time_fst,volume_pair,Function.comp_apply]
  have hv : volume (if p i (a,e) then a :: ys else ys) ≤ volume a+volume ys+1 := by
    have hc := volume_cons a ys
    split <;> omega
  omega

theorem foldTime_filterBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (e : γ i) (T : ℕ) (xs ys : List (α i))
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    Realizer.foldTime ((filterBody P).specialize i) (e,ys) xs ≤
      xs.length*(T+30000*(volume xs+volume e+volume ys+1))+1 := by
  induction xs generalizing ys with
  | nil => simp only [Realizer.foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have ha := hT a (by simp)
    have ht := time_filterBody P i a e ys
    have hi := ih (if p i (a,e) then a :: ys else ys) (fun a ha => hT a (by simp [ha]))
    have hv : volume (if p i (a,e) then a :: ys else ys) ≤ volume a+volume ys+1 := by
      have hc := volume_cons a ys
      split <;> omega
    simp only [Realizer.foldTime]
    change (filterBody P).time i (a,(e,ys))+
      Realizer.foldTime ((filterBody P).specialize i) (e,if p i (a,e) then a :: ys else ys) xs+
      20*(volume (a :: xs)+volume (e,ys)+volume (e,if p i (a,e) then a :: ys else ys)+1) ≤ _
    simp only [volume_pair,volume_cons,List.length_cons] at hi ⊢
    nlinarith [volume_pos a,volume_pos xs,volume_pos ys,volume_pos e]

theorem time_filter {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    P.filter.time i (xs,e) ≤ 100000*(xs.length+1)*(T+volume xs+volume e+1) := by
  have hf := foldTime_filterBody P i e T xs [] hT
  have hr := time_reverse i ((xs.filter (fun a => p i (a,e))).reverse)
  have hv := volume_filter_le (fun a => p i (a,e)) xs
  have hl := List.length_filter_le (fun a => p i (a,e)) xs
  simp only [volume_nil,List.length_reverse,volume_reverse] at hf hr
  simp only [filter,time_congr,time_comp,time_pair,time_fst,time_snd,time_nil,time_fold,
    Function.comp_apply,filter_fold_eq,List.append_nil,volume_pair,volume_nil,volume_reverse]
  nlinarith [volume_pos xs,volume_pos e]

theorem time_optionMap {f : ∀ i, α i × γ i → β i} (R : Uniform f)
    (i : I) (o : Option (α i)) (e : γ i) (T V : ℕ)
    (hT : ∀ a ∈ o, R.time i (a,e) ≤ T) (hV : ∀ a ∈ o, volume (f i (a,e)) ≤ V) :
    R.optionMap.time i (o,e) ≤ 1000000*(T+volume o+volume e+V+1) := by
  have hl : o.toList.length ≤ 1 := by cases o <;> simp
  have hv : volume (o.toList.map (fun a => f i (a,e))) ≤ V+3 := by
    cases o with
    | none => simp only [Option.toList_none,List.map_nil,volume_nil]; omega
    | some a =>
      have hv := hV a rfl
      simp only [Option.toList_some,List.map_cons,List.map_nil,volume_cons,volume_nil]
      omega
  have hm := time_map R i o.toList e T (fun a ha => hT a (by simpa using ha))
  have hh := time_head?_le i (o.toList.map (fun a => f i (a,e)))
  simp only [optionMap,time_congr,time_comp,onFst,time_pair,optionToList,time_reinterpret,
    time_fst,time_snd,Function.comp_apply,volume_pair,volume_optionToList] at hm ⊢
  nlinarith [volume_pos o,volume_pos e]

theorem time_getD_le (i : I) (o : Option (α i)) (a : α i) :
    getD.time i (o,a) ≤ 10000*(volume o+volume a+1) := by
  cases o with
  | none =>
    simp only [getD,time_congr,time_comp,time_pair,time_fst,time_snd,optionToList,time_reinterpret,
      time_fold,Function.comp_apply,Realizer.foldTime,Option.toList_none,volume_pair,volume_none,volume_nil]
    omega
  | some b =>
    simp only [getD,time_congr,time_comp,time_pair,time_fst,time_snd,optionToList,time_reinterpret,
      time_fold,Function.comp_apply,Realizer.foldTime,Option.toList_some,volume_pair,volume_some,volume_cons,volume_nil]
    simp only [Realizer.time,Uniform.specialize,Uniform.fst,Routine.select,volume,enc_pair,Data.size_pair]
    omega

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u33} {α : I → Type u34} {β : I → Type u35} {γ : I → Type u36}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_anyBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (a : α i) (e : γ i) (b : Bool) :
    (anyBody P).time i (a,(e,b)) ≤ P.time i (a,e)+100000*(volume a+volume e+1) := by
  have hp := volume_bool (p i (a,e))
  have hb := volume_bool b
  have ho := volume_bool (b || p i (a,e))
  have ht := Realizer.time_or_le (b,p i (a,e))
  simp only [anyBody,time_pair,time_comp,time_fst,time_snd,time_uniform,volume_pair,Function.comp_apply]
  omega

theorem time_any {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    P.any.time i (xs,e) ≤ 10000000*(xs.length+1)*(T+volume xs+volume e+1) := by
  have hf := time_fold_le (anyBody P) i xs (fun b => b.1 = e)
    (T+100000*(volume xs+volume e+1)) (volume e+4)
    (by rintro ⟨e',b⟩ hb; dsimp only at hb; subst e'; rw [volume_pair]; have := volume_bool b; omega)
    (by intro a ha b hb; exact hb)
    (by intro a ha b hb
        have h := time_anyBody P i a e b.2
        have ht := hT a ha
        have hv := volume_mem_le ha
        subst e
        exact h.trans (by omega)) (e,Bool.false) rfl
  have hv := volume_bool (xs.any (fun a => p i (a,e)))
  simp only [any,time_congr,time_comp,time_pair,time_fst,time_snd,time_false,
    Function.comp_apply,any_fold_eq,Bool.false_or,volume_pair,volume_bool_false]
  nlinarith [volume_pos xs,volume_pos e]

theorem time_all {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    P.all.time i (xs,e) ≤ 1000000000000*(xs.length+1)*(T+volume xs+volume e+1) := by
  have hf := time_any (P.comp (Realizer.not.uniform I)) i xs e (T+10040) (by
    intro a ha
    have ht := hT a ha
    have hn := Realizer.time_not_le (p i (a,e))
    have hv := volume_bool (p i (a,e))
    simp only [time_comp,time_uniform]
    omega)
  have hn := Realizer.time_not_le (xs.any (fun a => !(p i (a,e))))
  have hv := volume_bool (xs.any (fun a => !(p i (a,e))))
  simp only [all,time_congr,time_comp,time_uniform,Function.comp_apply]
  nlinarith [volume_pos xs,volume_pos e]

theorem time_find? {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    P.find?.time i (xs,e) ≤ 1000000*(xs.length+1)*(T+volume xs+volume e+1) := by
  have hf := time_filter P i xs e T hT
  have hh := time_head?_le i (xs.filter (fun a => p i (a,e)))
  have hv := volume_filter_le (fun a => p i (a,e)) xs
  simp only [find?,time_congr,time_comp]
  nlinarith [volume_pos xs,volume_pos e]

theorem time_flatMap {f : ∀ i, α i × γ i → List (β i)} (R : Uniform f)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T) :
    R.flatMap.time i (xs,e) ≤ 100000*(xs.length+(xs.flatMap (fun a => f i (a,e))).length+1)*
      (T+volume xs+volume e+volume (xs.map (fun a => f i (a,e)))+1) := by
  have hm := time_map R i xs e T hT
  have hf := time_flatten i (xs.map (fun a => f i (a,e)))
  simp only [List.length_map,← List.flatMap_def] at hf
  simp only [flatMap,time_congr,time_comp]
  nlinarith [volume_pos xs,volume_pos e,volume_pos (xs.map (fun a => f i (a,e)))]

omit [∀ i, Coding (α i)] in
theorem volume_map_options {i : I} (xs : List (α i)) (f : α i → Option (β i)) :
    volume (xs.map (fun a => (f a).toList)) = volume (xs.filterMap f)+2*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases ho : f a <;> simp only [List.map_cons,List.filterMap_cons,ho,Option.toList_none,
      Option.toList_some,volume_cons,volume_nil,List.length_cons,ih] <;> omega

theorem time_filterMap {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f)
    (i : I) (xs : List (α i)) (e : γ i) (T V : ℕ)
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T)
    (hV : ∀ a ∈ xs, volume (f i (a,e)) ≤ V) :
    R.filterMap.time i (xs,e) ≤ 10000000*(xs.length+1)*
      (T+volume xs+volume e+volume (xs.filterMap (fun a => f i (a,e)))+V+1) := by
  have hm := time_flatMap (R.comp optionToList) i xs e (T+11*V+12) (by
    intro a ha
    have ht := hT a ha
    have hv := hV a ha
    simp only [time_comp,optionToList,time_reinterpret]
    omega)
  have he : xs.flatMap (fun a => (f i (a,e)).toList) = xs.filterMap (fun a => f i (a,e)) := by
    clear hm hT hV
    induction xs with
    | nil => rfl
    | cons a xs ih => cases ho : f i (a,e) <;> simp [ho,ih]
  simp only [Function.comp_apply] at hm
  rw [he,volume_map_options] at hm
  have hl := List.length_filterMap_le (f := fun a => f i (a,e)) (l := xs)
  have hv := length_le_volume xs
  simp only [filterMap,time_congr]
  nlinarith [volume_pos xs,volume_pos e]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler

@[simp] theorem volume_replicate_unit (m : ℕ) : volume (List.replicate m ()) = 2*m+1 := by
  change (enc (List.replicate m ())).size = _
  rw [Realizer.encode_replicate_unit]
  exact volume_nat m

namespace Uniform
variable {I : Type u37} {α : I → Type u38} {β : I → Type u39} {γ : I → Type u40}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

omit [∀ i, Coding (β i)] [∀ i, Coding (γ i)] in
theorem foldTime_iterate_le {f : ∀ i, α i → α i} (R : Uniform f)
    (i : I) (m : ℕ) (a : α i) (T V : ℕ)
    (hT : ∀ j < m, R.time i ((f i)^[j] a) ≤ T)
    (hV : ∀ j ≤ m, volume ((f i)^[j] a) ≤ V) :
    Realizer.foldTime ((snd.comp R : Uniform (fun i (x : Unit × α i) => f i x.2)).specialize i)
      a (List.replicate m ()) ≤ m*(T+100*(V+m+1))+1 := by
  induction m generalizing a with
  | zero => simp only [List.replicate_zero,Realizer.foldTime,Nat.zero_mul,Nat.zero_add]; rfl
  | succ m ih =>
    have hv := hV 0 (by omega)
    have hw := hV 1 (by omega)
    have ht := hT 0 (by omega)
    have hi := ih (f i a)
      (fun j hj => by simpa only [Function.iterate_succ_apply] using hT (j+1) (by omega))
      (fun j hj => by simpa only [Function.iterate_succ_apply] using hV (j+1) (by omega))
    simp only [Function.iterate_zero_apply,Function.iterate_one] at hv hw ht
    rw [List.replicate_succ,Realizer.foldTime]
    change (snd.comp R).time i ((),a)+_+20*(volume (() :: List.replicate m ())+volume a+volume (f i a)+1) ≤ _
    simp only [time_comp,time_snd,volume_pair,volume_unit,volume_cons,volume_replicate_unit,Function.comp_apply]
    nlinarith

omit [∀ i, Coding (β i)] [∀ i, Coding (γ i)] in
theorem time_iterate_le {f : ∀ i, α i → α i} (R : Uniform f)
    (i : I) (m : ℕ) (a : α i) (T V : ℕ)
    (hT : ∀ j < m, R.time i ((f i)^[j] a) ≤ T)
    (hV : ∀ j ≤ m, volume ((f i)^[j] a) ≤ V) :
    R.iterate.time i (m,a) ≤ 10000*(m+1)*(T+V+m+1) := by
  have hf := foldTime_iterate_le R i m a T V hT hV
  have hv := hV 0 (Nat.zero_le _)
  simp only [Function.iterate_zero_apply] at hv
  simp only [iterate,time_congr,time_comp,onFst,time_pair,time_fst,time_snd,time_uniform,
    Realizer.unroll,Realizer.time_reinterpret,Function.comp_apply,time_fold,volume_pair,
    volume_nat,volume_replicate_unit]
  nlinarith

theorem time_firstResult {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f)
    (i : I) (xs : List (α i)) (e : γ i) (T V : ℕ)
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T)
    (hV : ∀ a ∈ xs, volume (f i (a,e)) ≤ V) :
    R.firstResult.time i (xs,e) ≤ 100000000*(xs.length+1)*
      (T+volume xs+volume e+(xs.length+1)*(V+1)+1) := by
  have hv : volume (xs.filterMap (fun a => f i (a,e))) ≤ (xs.length+1)*(V+1) := by
    have h := volume_list_le (xs.filterMap (fun a => f i (a,e))) V (by
      intro b hb
      obtain ⟨a,ha,hb⟩ := List.mem_filterMap.mp hb
      have hx := hV a ha
      rw [hb,volume_some] at hx
      omega)
    have hl := List.length_filterMap_le (f := fun a => f i (a,e)) (l := xs)
    nlinarith
  have hf := time_filterMap R i xs e T V hT hV
  have hh := time_head?_le i (xs.filterMap (fun a => f i (a,e)))
  simp only [firstResult,time_comp]
  nlinarith [volume_pos xs,volume_pos e]

end Uniform
end ThreeMachine.StackCompiler
end

end OAI
