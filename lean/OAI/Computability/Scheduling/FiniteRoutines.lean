import OAI.Computability.Scheduling.UniformRoutines

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15

section

namespace ThreeMachine.StackCompiler

instance (n : ℕ) : Coding (Fin n) := ⟨fun x => enc x.val⟩
instance (n : ℕ) : Coding (Finset (Fin n)) := ⟨fun s => enc (s.sort (· ≤ ·))⟩

@[simp] theorem enc_fin {n : ℕ} (x : Fin n) : enc x = enc x.val := rfl
@[simp] theorem volume_fin {n : ℕ} (x : Fin n) : volume x = 2*x.val+1 := volume_nat x.val
@[simp] theorem enc_finset {n : ℕ} (s : Finset (Fin n)) :
    enc s = enc (s.sort (· ≤ ·)) := rfl

structure Cardinal (n : ℕ) where
  trivial : Unit
instance (n : ℕ) : Coding (Cardinal n) := ⟨fun _ => enc n⟩

structure Universe (n : ℕ) where
  trivial : Unit
instance (n : ℕ) : Coding (Universe n) := ⟨fun _ => enc (List.finRange n)⟩

theorem enc_list_map {α : Type u1} {β : Type u2} [Coding α] [Coding β] (f : α → β)
    (hf : ∀ x, enc (f x) = enc x) (xs : List α) : enc (xs.map f) = enc xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,enc_cons,hf,ih]

theorem sort_filter {n : ℕ} (s : Finset (Fin n)) (p : Fin n → Bool) :
    (s.filter (fun x => p x)).sort (· ≤ ·) = (s.sort (· ≤ ·)).filter p := by
  have he : ((s.sort (· ≤ ·)).filter p).toFinset = s.filter (fun x => p x) := by
    ext x; simp
  rw [← he]
  exact (List.toFinset_sort (· ≤ ·) ((s.sort_nodup (· ≤ ·)).filter p)).mpr
    ((s.pairwise_sort (· ≤ ·)).filter p)

namespace Uniform

def finVal : Uniform (fun n (x : Fin n) => x.val) := reinterpret _ (fun _ _ => rfl)

def finEq : Uniform (fun n (x : Fin n × Fin n) => decide (x.1 = x.2)) :=
  (((fst.comp finVal).pair (snd.comp finVal)).comp (Realizer.eqNat.uniform ℕ)).congr
    (fun _ x => by simp only [Function.comp_apply,Fin.val_inj])

def cardinal : Uniform (fun n (_ : Cardinal n) => n) := reinterpret _ (fun _ _ => rfl)

def universeList : Uniform (fun n (_ : Universe n) => List.finRange n) :=
  reinterpret _ (fun _ _ => rfl)

def universeSet : Uniform (fun n (_ : Universe n) => (Finset.univ : Finset (Fin n))) :=
  reinterpret _ (fun n _ => by simp only [enc_finset,Fin.sort_univ]; rfl)

def setList : Uniform (fun n (s : Finset (Fin n)) => s.sort (· ≤ ·)) :=
  reinterpret _ (fun _ _ => rfl)

def setEmpty : Uniform (fun n (_ : Universe n) => (∅ : Finset (Fin n))) where
  transform := fun _ => .nil
  charge := _
  routine := Routine.nil
  correct _ _ := by simp only [enc_finset,Finset.sort_empty]; rfl

def setIsEmpty : Uniform (fun n (s : Finset (Fin n)) => decide (s = ∅)) :=
  ((setList.comp isCons).comp (Realizer.not.uniform ℕ)).congr (fun _ x => by
    by_cases h : x = ∅
    · subst x; simp
    · have hh : x.sort (· ≤ ·) ≠ [] := by
        intro he; have := congrArg List.toFinset he
        exact h (by simpa only [Finset.sort_toFinset,List.toFinset_nil] using this)
      simp [Function.comp_apply,List.isEmpty_eq_false_iff,hh,h])

def setCard : Uniform (fun n (s : Finset (Fin n)) => s.card) :=
  (setList.comp length).congr (fun _ _ => Finset.length_sort (· ≤ ·))

def setFilter {γ : ℕ → Type u3} [∀ n, Coding (γ n)]
    {p : ∀ n, Fin n × γ n → Bool} (P : Uniform p) :
    Uniform (fun n (x : Finset (Fin n) × γ n) => x.1.filter (fun a => p n (a,x.2))) where
  transform := (setList.onFst.comp P.filter).transform
  charge := (setList.onFst.comp P.filter).charge
  routine := (setList.onFst.comp P.filter).routine
  correct n x := by
    rw [(setList.onFst.comp P.filter).correct]
    simp only [Function.comp_apply,enc_finset,sort_filter]

def setMem : Uniform (fun n (x : Fin n × Finset (Fin n)) => decide (x.1 ∈ x.2)) :=
  ((((snd.comp setList).pair fst).comp finEq.any)).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_eq_true,decide_eq_true_eq]
    simp)

def setInter : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => x.1 ∩ x.2) :=
  setMem.setFilter.congr (fun _ x => by ext a; simp)

def setDiff : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => x.1 \ x.2) :=
  (setMem.comp (Realizer.not.uniform ℕ)).setFilter.congr (fun _ x => by ext a; simp)

def setSubset : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => decide (x.1 ⊆ x.2)) :=
  ((setList.onFst).comp setMem.all).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.all_eq_true,decide_eq_true_eq,Finset.mem_sort]
    rfl)

def setEq : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => decide (x.1 = x.2)) :=
  ((setSubset.pair (swap.comp setSubset)).comp (Realizer.and.uniform ℕ)).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp [Finset.Subset.antisymm_iff])

def setDisjoint : Uniform (fun n (x : Finset (Fin n) × Finset (Fin n)) => decide (Disjoint x.1 x.2)) :=
  (setInter.comp setIsEmpty).congr (fun _ x => by
    simp only [Function.comp_apply,Finset.disjoint_iff_inter_eq_empty])

def setUnionBody : Uniform (fun n (x : Fin n × (Finset (Fin n) × Finset (Fin n))) =>
    decide (x.1 ∈ x.2.1 ∨ x.1 ∈ x.2.2)) :=
  ((((fst.pair (snd.comp fst)).comp setMem).pair
      ((fst.pair (snd.comp snd)).comp setMem)).comp (Realizer.or.uniform ℕ)).congr (fun _ _ => by simp)

def setUnion : Uniform (fun n (x : Universe n × (Finset (Fin n) × Finset (Fin n))) =>
    x.2.1 ∪ x.2.2) :=
  (((fst.comp universeSet).pair snd).comp setUnionBody.setFilter).congr (fun _ x => by
    ext a; simp)

def setCompl : Uniform (fun n (x : Universe n × Finset (Fin n)) => x.2ᶜ) :=
  (((fst.comp universeSet).pair snd).comp setDiff).congr (fun _ x => (Finset.compl_eq_univ_sdiff x.2).symm)

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Realizer

def rangeStep : Realizer (fun x : ℕ × List ℕ => (x.1+1,x.1 :: x.2)) :=
  (fst.comp succ).pair cons

theorem rangeStep_iterate (n : ℕ) :
    (fun x : ℕ × List ℕ => (x.1+1,x.1 :: x.2))^[n] (0,[]) = (n,(List.range n).reverse) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih]; simp [List.range_succ]

def range : Realizer List.range :=
  (((id.pair (zero.pair nil)).comp rangeStep.iterate).comp (snd.comp reverse)).congr (fun n => by
    simp only [Function.comp_apply,rangeStep_iterate,List.reverse_reverse,id_eq])

end Realizer

theorem finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last,List.map_append,List.map_map]
    simpa only [Function.comp_def,Fin.val_castSucc,List.map_cons,List.map_nil,Fin.val_last,ih]
      using (List.range_succ (n := n)).symm

namespace Uniform

def makeUniverse : Uniform (fun n (_ : Cardinal n) => (Universe.mk () : Universe n)) where
  transform := Realizer.range.transform
  charge := Realizer.range.charge
  routine := Realizer.range.routine
  correct n _ := by
    change Realizer.range.transform (enc n) = enc (List.finRange n)
    rw [Realizer.range.correct,← finRange_val]
    exact enc_list_map Fin.val (fun _ => rfl) _

def numLength : Uniform (fun (_ : ℕ) (x : List ℕ) => x.length) := length

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
variable {α : Type u4} [Coding α]

theorem volume_append (xs ys : List α) : volume (xs ++ ys)+1 = volume xs+volume ys := by
  induction xs with
  | nil => simp [Nat.add_comm]
  | cons a xs ih => simp only [List.cons_append,volume_cons]; omega

theorem volume_reverse (xs : List α) : volume xs.reverse = volume xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.reverse_cons]
    have := volume_append xs.reverse [a]
    simp only [volume_cons,volume_nil,ih] at this ⊢
    omega

theorem volume_filter (p : α → Bool) (xs : List α) : volume (xs.filter p) ≤ volume xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases he : p a <;> simp only [List.filter_cons,he,Bool.false_eq_true,ite_false,ite_true,volume_cons]
    · omega
    · omega

namespace Uniform
variable {I : Type u5} {α : I → Type u6} {β : I → Type u7} {γ : I → Type u8}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}

@[simp] theorem time_id (i : I) (x : α i) :
    (id : Uniform (fun i (x : α i) => x)).time i x = volume x+2 := rfl
@[simp] theorem time_fst (i : I) (x : α i × β i) :
    (fst : Uniform (fun i (x : α i × β i) => x.1)).time i x = volume x+2 := rfl
@[simp] theorem time_snd (i : I) (x : α i × β i) :
    (snd : Uniform (fun i (x : α i × β i) => x.2)).time i x = volume x+2 := rfl
@[simp] theorem time_nil (i : I) (x : α i) :
    (nil : Uniform (fun i (_ : α i) => ([] : List (β i)))).time i x = 2 := rfl
@[simp] theorem time_unit (i : I) (x : α i) :
    (unit : Uniform (fun i (_ : α i) => ())).time i x = 2 := rfl
@[simp] theorem time_zero (i : I) (x : α i) :
    (zero : Uniform (fun i (_ : α i) => (0 : ℕ))).time i x = 2 := rfl
@[simp] theorem time_false (i : I) (x : α i) :
    (false : Uniform (fun i (_ : α i) => Bool.false)).time i x = 2 := rfl
@[simp] theorem time_congr {f' : ∀ i, α i → β i} (R : Uniform f)
    (h : ∀ i x, f i x = f' i x) (i : I) (x : α i) :
    (R.congr h).time i x = R.time i x := rfl
@[simp] theorem time_reinterpret (f : ∀ i, α i → β i) (h : ∀ i x, enc (f i x) = enc x)
    (i : I) (x : α i) : (reinterpret f h).time i x = volume x+2 := rfl
@[simp] theorem time_cons (i : I) (x : α i × List (α i)) : cons.time i x = volume x+2 := rfl

theorem time_comp (R : Uniform f) (S : Uniform g) (i : I) (x : α i) :
    (R.comp S).time i x = R.time i x+S.time i (f i x)+10*(volume (f i x)+1) := by
  simp only [comp,time,Routine.comp,R.correct,volume]

theorem time_pair {g : ∀ i, α i → γ i} (R : Uniform f) (S : Uniform g) (i : I) (x : α i) :
    (R.pair S).time i x = R.time i x+S.time i x+20*(volume x+volume (f i x)+volume (g i x)+1) := by
  simp only [pair,time,Routine.pair,R.correct,S.correct,volume]

theorem time_fold {F : ∀ i, α i × β i → β i} (R : Uniform F) (i : I) (x : List (α i) × β i) :
    R.fold.time i x = 2*volume x+6+Realizer.foldTime (R.specialize i) x.2 x.1 :=
  (R.specialize i).time_fold x

theorem time_choose {g : ∀ i, α i → β i} (R : Uniform f) (S : Uniform g)
    (i : I) (x : Bool × α i) :
    (R.choose S).time i x = ((snd (α := fun _ : I => Bool) (β := α)).comp R).time i x+
      ((snd (α := fun _ : I => Bool) (β := α)).comp S).time i x+
      30*(volume x+volume (f i x.2)+volume (g i x.2)+1) :=
  (R.specialize i).time_choose (S.specialize i) x

theorem time_constant {δ : Type u9} [Coding δ] (a : δ) (i : I) (x : α i) :
    (constant a : Uniform (fun i (_ : α i) => a)).time i x =
      (2*volume a+1)*(20*volume x+50*volume a+50) := rfl

theorem time_reverse (i : I) (xs : List (α i)) :
    reverse.time i xs ≤ 200*(xs.length+1)*(volume xs+1) := by
  have hf : ∀ (xs ys : List (α i)),
      Realizer.foldTime ((cons : Uniform (fun i (x : α i × List (α i)) => x.1 :: x.2)).specialize i) ys xs ≤
        xs.length * (100*(volume xs+volume ys+1))+1 := by
    intro xs; induction xs with
    | nil => intro ys; simp only [Realizer.foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
    | cons a xs ih =>
      intro ys
      have hh := ih (a :: ys)
      change volume (a,ys)+2+Realizer.foldTime _ (a :: ys) xs+
        20*(volume (a :: xs)+volume ys+volume (a :: ys)+1) ≤ _
      simp only [volume_pair,volume_cons,List.length_cons] at hh ⊢
      nlinarith [volume_pos a,volume_pos xs,volume_pos ys]
  simp only [reverse,time_congr,time_comp,time_pair,time_id,time_nil,time_fold,volume_pair,volume_nil]
  have hh := hf xs []
  simp only [volume_nil] at hh
  nlinarith [volume_pos xs]

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

instance {α : Type u10} [Coding α] (n : ℕ) : Coding (Fin n → α) := ⟨fun f => enc (List.ofFn f)⟩

@[simp] theorem enc_function {α : Type u11} [Coding α] {n : ℕ} (f : Fin n → α) :
    enc f = enc (List.ofFn f) := rfl

namespace Uniform
variable {I : Type u12} {α : I → Type u13} [∀ i, Coding (α i)]

def tail : Uniform (fun (i : I) (xs : List (α i)) => xs.tail) :=
  ⟨Data.tail,_,Routine.select Bool.false,fun _ xs => by cases xs <;> rfl⟩

def drop : Uniform (fun (i : I) (x : List (α i) × ℕ) => x.1.drop x.2) :=
  (swap.comp tail.iterate).congr (fun i x => by
    dsimp only [Function.comp_apply]
    have h : ∀ (n : ℕ) (xs : List (α i)), List.tail^[n] xs = xs.drop n := by
      intro n; induction n with
      | zero => intro xs; rfl
      | succ n ih => intro xs; rw [Function.iterate_succ_apply,ih,List.drop_tail]
    exact h x.2 x.1)

def getElem? : Uniform (fun (i : I) (x : List (α i) × ℕ) => x.1[x.2]?) :=
  (drop.comp head?).congr (fun _ _ => by simp only [Function.comp_apply,List.head?_drop])

def getElemD : Uniform (fun (i : I) (x : (List (α i) × ℕ) × α i) => x.1.1.getD x.1.2 x.2) :=
  (getElem?.onFst.comp getD).congr (fun _ _ => List.getD_eq_getElem?_getD.symm)

end Uniform

namespace Uniform
variable {α : ℕ → Type u14} {β : ℕ → Type u15} [∀ n, Coding (α n)] [∀ n, Coding (β n)]

def functionList : Uniform (fun n (f : Fin n → α n) => List.ofFn f) :=
  reinterpret _ (fun _ _ => rfl)

def functionGetOption : Uniform (fun n (x : (Fin n → α n) × Fin n) => Option.some (x.1 x.2)) :=
  (((fst.comp functionList).pair (snd.comp finVal)).comp getElem?).congr (fun _ x => by
    simp only [Function.comp_apply,List.getElem?_ofFn,dite_eq_left x.2.isLt])

def functionGet : Uniform (fun n (x : (Fin n → α n) × Fin n) => x.1 x.2) where
  transform := Data.head ∘ (functionGetOption (α := α)).transform
  charge := _
  routine := (functionGetOption (α := α)).routine.comp (Routine.select true)
  correct n x := by
    simp only [Function.comp_apply,(functionGetOption (α := α)).correct,enc_some,Data.head]

def vectorMap {f : ∀ n, Fin n × α n → β n} (R : Uniform f) :
    Uniform (fun n (x : Universe n × α n) => fun v => f n (v,x.2)) where
  transform := (universeList.onFst.comp R.map).transform
  charge := (universeList.onFst.comp R.map).charge
  routine := (universeList.onFst.comp R.map).routine
  correct n x := by
    rw [(universeList.onFst.comp R.map).correct]
    simp only [Function.comp_apply,enc_function,List.ofFn_eq_map]

end Uniform
end ThreeMachine.StackCompiler

end

end OAI
