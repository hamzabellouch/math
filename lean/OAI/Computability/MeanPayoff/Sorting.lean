import OAI.Computability.MeanPayoff.OperatorDevices

namespace OAI

section

namespace MeanPayoff.RegisterBits.Flow

theorem finish_at {K : ℕ} (P : Program K) (p : Fin P.nodes) (s t : Fin K → List Bool)
    (out : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (hm : advance (P.block p) bits ⟨some (P.block p).start,s,out⟩ N = ⟨none,t,out⟩)
    (hn : ∀ bit, P.next p (t (P.read p)).head? bit = none) :
    ∃ d ≤ N+1, advance (compile P) bits (state P p s out) d = ⟨none,t,out⟩ := by
  obtain ⟨d,hd,he⟩ := macro_runs P p s out bits N (by rw [hm])
  rw [hm] at he
  refine ⟨d+1,by omega,?_⟩
  simp only [advance,he,step_boundary,hn]

end MeanPayoff.RegisterBits.Flow

namespace MeanPayoff.TreeDevice.Tail
open RegisterBits BinaryData

noncomputable abbrev discard {α : Type} (ea : α → Data) := Forest.drop ea (fun _ => [])

noncomputable abbrev flow {α : Type} (ea : α → Data) : Flow.Program 5 where
  nodes := 2
  start := 0
  block := ![skip,(discard ea).program]
  read _ := 0
  next p top _ := if p=0 ∧ top=some true then some ⟨1,.pop,none⟩ else none

noncomputable abbrev program {α : Type} (ea : α → Data) := Flow.compile (flow ea)

noncomputable def limit {α : Type} (ea : α → Data) : List α → ℕ
  | [] => 2
  | x::_ => (discard ea).limit x+3

theorem runs {α : Type} (ea : α → Data) (xs : List α) (suffix out : List Bool) :
    Reaches (program ea) ⟨some (program ea).start,store (listTree ea xs) suffix,out⟩
      ⟨none,store (listTree ea xs.tail) suffix,out⟩ (limit ea xs) := by
  cases xs with
  | nil =>
    intro bits
    exact Flow.finish_at (flow ea) 0 _ _ out bits 1 rfl (by intros; rfl)
  | cons x xs =>
    let s₀ := store (listTree ea (x::xs)) suffix
    let s₁ := core (encode (ea x)++(encode (listTree ea xs)++suffix)) [] []
    have h₀ : Reaches (program ea) (Flow.state (flow ea) 0 s₀ out)
        (Flow.state (flow ea) 1 s₁ out) 2 := by
      intro bits
      apply Flow.hop_update (flow ea) 0 1 s₀ s₀ s₁ out bits 1 .pop rfl (by intros; rfl)
      change Function.update (core (encode (listTree ea (x::xs))++suffix) [] []) 0
        (BinaryStack.applyOp .pop (encode (listTree ea (x::xs))++suffix)) = s₁
      rw [core_update]
      simp only [encode_listTree_cons,List.cons_append,BinaryStack.applyOp,List.tail_cons]
      simp only [List.append_assoc]
      rfl
    have h₁ : Reaches (program ea) (Flow.state (flow ea) 1 s₁ out)
        ⟨none,store (listTree ea xs) suffix,out⟩ ((discard ea).limit x+1) := by
      intro bits
      have h := (discard ea).correct x (encode (listTree ea xs)++suffix) out bits
      simp only [Forest.stack,Forest.encode_cons,Forest.encode_nil,List.append_nil] at h
      exact Flow.finish (flow ea) 1 _ _ out bits _ h (by intros; rfl)
    exact (h₀.trans h₁).mono (by dsimp only [limit]; omega)

noncomputable def device {α : Type} (ea : α → Data) :
    Device (listTree ea) (listTree ea) List.tail :=
  ofProgram _ _ _ (program ea) (limit ea) (fun xs suffix out bits => (runs ea xs suffix out).pad rfl bits)

end MeanPayoff.TreeDevice.Tail

namespace MeanPayoff.TreeDevice.Halve
open BinaryData

def halve (w : SignedBits.Word) : SignedBits.Word := ⟨w.sign,w.digits.tail⟩

theorem halve_val (w : SignedBits.Word) : (halve w).val = w.val / 2 := by
  have hv := SignedBits.val_uncons w.sign w.digits
  change w.val = (SignedBits.head w.sign w.digits).toNat +
    2*(SignedBits.Word.mk w.sign w.digits.tail).val at hv
  have hb : (SignedBits.head w.sign w.digits).toNat ≤ 1 := by
    cases (SignedBits.head w.sign w.digits) <;> decide
  change (SignedBits.Word.mk w.sign w.digits.tail).val = _
  omega

theorem listTree_boolData (bs : List Bool) : listTree boolData bs = listData bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [listTree_cons,listData,ih]

noncomputable def device : Device wordData wordData halve := by
  let P := pairMap (identity boolData) (Tail.device boolData)
  refine ⟨P.program, (fun w => P.limit (w.sign,w.digits)),P.quiet,?_⟩
  intro w suffix out bits
  have h := P.correct (w.sign,w.digits) suffix out bits
  simpa only [product,id_eq,wordData,listData,listTree_boolData,halve] using h

def average (ab : SignedBits.Word × SignedBits.Word) := halve (Add.sumPair ab)

noncomputable def averageDevice : Device (product wordData wordData) wordData average :=
  compose Add.device device

theorem average_val (ab : SignedBits.Word × SignedBits.Word) :
    (average ab).val = (ab.1.val+ab.2.val)/2 := by
  rw [average,halve_val,Add.sumPair_val]

noncomputable def averageVectorDevice :
    Device (listTree (product wordData wordData)) (listTree wordData) (List.map average) :=
  Map.device averageDevice

theorem average_exact {n : ℕ} (a b : Fin n → SignedBits.Word) (i : Fin n) :
    (average (a i,b i)).val = (a i).val + ((b i).val-(a i).val)/2 := by
  rw [average_val]
  dsimp only
  omega

end MeanPayoff.TreeDevice.Halve
namespace MeanPayoff.TreeDevice
open RegisterBits BinaryData

def Device.recode {α β γ δ : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (ec : γ → Data) (ed : δ → Data) (i : γ → α) (h : γ → δ)
    (hin : ∀ x, ea (i x) = ec x) (hout : ∀ x, eb (f (i x)) = ed (h x)) : Device ec ed h where
  program := F.program
  limit x := F.limit (i x)
  quiet := F.quiet
  correct x suffix out bits := by
    rw [← hin x,← hout x]
    exact F.correct (i x) suffix out bits

noncomputable def pairSwap {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device (product ea eb) (product eb ea) (fun z => (z.2,z.1)) :=
  fanout (second ea eb) (first ea eb)

namespace Forest

def pushNil {α : Type} (x : α → Data) :
    Segment (fun z => ⟨[x z],[],[]⟩) (fun z => ⟨[Data.nil,x z],[],[]⟩) where
  program := bitOp 0 (.push false)
  limit _ := 2
  correct z suffix out bits := by
    rw [bitOp_runs]
    simp only [stack,encode_cons,encode_nil,List.append_nil,BinaryData.encode,List.cons_append,
      core_zero,BinaryStack.applyOp]
    apply Take.config_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl

end Forest
namespace Lists

noncomputable def nilPrefix {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device ea (product (listTree eb) ea) (fun x => ([],x)) :=
  Forest.toDevice _ _ _ <| (Forest.pushNil ea).seq
    (Forest.pair (fun _ => Data.nil) ea (fun _ => []) (fun _ => []) (fun _ => []))

noncomputable def nilSuffix {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device ea (product ea (listTree eb)) (fun x => (x,[])) :=
  compose (nilPrefix ea eb) (pairSwap (listTree eb) ea)

def consDevice {α : Type} (ea : α → Data) :
    Device (product ea (listTree ea)) (listTree ea) (fun z => z.1::z.2) :=
  (identity (product ea (listTree ea))).recode _ _ id (fun z => z.1::z.2)
    (by intros; rfl) (by intros; rfl)

noncomputable def consAcc {α : Type} (ea : α → Data) :
    Device (product (listTree ea) ea) (listTree ea) (fun z => z.2::z.1) :=
  compose (pairSwap (listTree ea) ea) (consDevice ea)

noncomputable def reverseDevice {α : Type} (ea : α → Data) :
    Device (listTree ea) (listTree ea) List.reverse :=
  (compose (nilPrefix (listTree ea) ea) (Fold.device (consAcc ea))).extFun (by
    intro xs
    exact List.foldl_cons_nil)

end Lists
end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice.Sort
open BinaryData

abbrev W := SignedBits.Word
abbrev Acc := W × List W
abbrev InStep := Acc × W

def carryStep (z : InStep) : Acc :=
  (Order.high (z.1.1,z.2),Order.low (z.1.1,z.2)::z.1.2)

noncomputable def pairDevice : Device (product (product wordData (listTree wordData)) wordData)
    (product wordData wordData) (fun z : InStep => (z.1.1,z.2)) :=
  fanout (compose (first (product wordData (listTree wordData)) wordData)
    (first wordData (listTree wordData))) (second (product wordData (listTree wordData)) wordData)

noncomputable def tailDevice : Device (product (product wordData (listTree wordData)) wordData)
    (listTree wordData) (fun z : InStep => z.1.2) :=
  compose (first (product wordData (listTree wordData)) wordData) (second wordData (listTree wordData))

noncomputable def carryDevice : Device (product (product wordData (listTree wordData)) wordData)
    (product wordData (listTree wordData)) carryStep :=
  fanout (compose pairDevice Order.maxDevice)
    (compose (fanout (compose pairDevice Order.minDevice) tailDevice) (Lists.consDevice wordData))

def insert (z : W × List W) : List W :=
  let a := Fold.fold carryStep (z.1,[]) z.2
  (a.1::a.2).reverse

noncomputable def initialDevice : Device (product wordData (listTree wordData))
    (product (product wordData (listTree wordData)) (listTree wordData))
    (fun z : W × List W => ((z.1,[]),z.2)) :=
  fanout (compose (first wordData (listTree wordData)) (Lists.nilSuffix wordData wordData))
    (second wordData (listTree wordData))

noncomputable def insertDevice : Device (product wordData (listTree wordData)) (listTree wordData) insert :=
  compose initialDevice (compose (Fold.device carryDevice)
    (compose (Lists.consDevice wordData) (Lists.reverseDevice wordData)))

def sort (xs : List W) : List W := xs.foldl (fun a w => insert (w,a)) []

noncomputable def sortDevice : Device (listTree wordData) (listTree wordData) sort := by
  let P := compose (Lists.nilPrefix (listTree wordData) wordData)
    (Fold.device (compose (pairSwap (listTree wordData) wordData) insertDevice))
  exact P.extFun (by intro xs; rfl)

def bubble (w : W) : List W → List W
  | [] => [w]
  | x::xs => Order.low (w,x)::bubble (Order.high (w,x)) xs

theorem fold_carry (w : W) (xs acc : List W) :
    let a := Fold.fold carryStep (w,acc) xs
    (a.1::a.2).reverse = acc.reverse++bubble w xs := by
  induction xs generalizing acc w with
  | nil => simp [Fold.fold,bubble]
  | cons x xs ih =>
    simpa only [Fold.fold,List.foldl_cons,carryStep,List.reverse_cons,List.append_assoc,
      List.singleton_append,bubble] using ih (Order.high (w,x)) (Order.low (w,x)::acc)

theorem insert_eq (z : W × List W) : insert z = bubble z.1 z.2 := by
  simpa only [insert,List.reverse_nil,List.nil_append] using fold_carry z.1 z.2 []

def bubbleInt (w : ℤ) : List ℤ → List ℤ
  | [] => [w]
  | x::xs => min w x::bubbleInt (max w x) xs

theorem bubble_val (w : W) (xs : List W) :
    (bubble w xs).map SignedBits.Word.val = bubbleInt w.val (xs.map SignedBits.Word.val) := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp only [bubble,List.map_cons,bubbleInt,Order.low_val,ih,Order.high_val]

end MeanPayoff.TreeDevice.Sort
namespace MeanPayoff.TreeDevice.Sort
open BinaryData

theorem bubble_perm (w : W) (xs : List W) : (bubble w xs).Perm (w::xs) := by
  induction xs generalizing w with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    by_cases h : Compare.testPair (w,x)=true
    · simpa only [bubble,Order.low,Order.high,h,ite_true] using (ih x).cons w
    · have hf : Compare.testPair (w,x)=false := Bool.eq_false_iff.mpr h
      simpa only [bubble,Order.low,Order.high,hf,Bool.false_eq_true,ite_false] using
        ((ih w).cons x).trans (List.Perm.swap _ _ _)

theorem bubbleInt_perm (w : ℤ) (xs : List ℤ) : (bubbleInt w xs).Perm (w::xs) := by
  induction xs generalizing w with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    by_cases h : w ≤ x
    · simpa only [bubbleInt,min_eq_left h,max_eq_right h] using (ih x).cons w
    · simpa only [bubbleInt,min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)] using
        ((ih w).cons x).trans (List.Perm.swap _ _ _)

theorem bubbleInt_sorted (w : ℤ) (xs : List ℤ) (hs : xs.Pairwise (· ≤ ·)) :
    (bubbleInt w xs).Pairwise (· ≤ ·) := by
  induction xs generalizing w with
  | nil => simp [bubbleInt]
  | cons x xs ih =>
    rw [List.pairwise_cons] at hs
    rw [bubbleInt,List.pairwise_cons]
    refine ⟨?_,ih _ hs.2⟩
    intro y hy
    have hm := (bubbleInt_perm (max w x) xs).mem_iff.mp hy
    rcases List.mem_cons.mp hm with rfl | hy
    · exact (min_le_left w x).trans (le_max_left w x)
    · exact (min_le_right w x).trans (hs.1 y hy)

theorem insert_perm (w : W) (xs : List W) : (insert (w,xs)).Perm (w::xs) := by
  rw [insert_eq]
  exact bubble_perm w xs

theorem insert_sorted (w : W) (xs : List W) (hs : (xs.map SignedBits.Word.val).Pairwise (· ≤ ·)) :
    ((insert (w,xs)).map SignedBits.Word.val).Pairwise (· ≤ ·) := by
  rw [insert_eq,bubble_val]
  exact bubbleInt_sorted _ _ hs

theorem fold_sort_perm (xs acc : List W) :
    (xs.foldl (fun a w => insert (w,a)) acc).Perm (acc++xs) := by
  induction xs generalizing acc with
  | nil => simp
  | cons w xs ih =>
    change (xs.foldl _ (insert (w,acc))).Perm _
    apply (ih (insert (w,acc))).trans
    apply ((insert_perm w acc).append_right xs).trans
    simpa only [List.cons_append,List.nil_append,List.append_assoc,List.singleton_append] using
      (show ([w]++acc).Perm (acc++[w]) from List.perm_append_comm).append_right xs

theorem fold_sort_sorted (xs acc : List W) (hs : (acc.map SignedBits.Word.val).Pairwise (· ≤ ·)) :
    ((xs.foldl (fun a w => insert (w,a)) acc).map SignedBits.Word.val).Pairwise (· ≤ ·) := by
  induction xs generalizing acc with
  | nil => exact hs
  | cons w xs ih => exact ih _ (insert_sorted _ _ hs)

theorem sort_perm (xs : List W) : (sort xs).Perm xs := by
  simpa only [sort,List.nil_append] using fold_sort_perm xs []

theorem sort_sorted (xs : List W) : ((sort xs).map SignedBits.Word.val).Pairwise (· ≤ ·) :=
  fold_sort_sorted xs [] (by simp)

theorem sort_values (xs : List W) :
    (sort xs).map SignedBits.Word.val = (xs.map SignedBits.Word.val).mergeSort (· ≤ ·) := by
  exact List.Perm.eq_of_pairwise' (sort_sorted xs) (List.pairwise_mergeSort' (· ≤ ·) _)
    (((sort_perm xs).map _).trans (List.mergeSort_perm _ _).symm)

theorem insert_size (w : W) (xs : List W) :
    treeSize (listTree wordData (insert (w,xs))) = treeSize (wordData w)+treeSize (listTree wordData xs)+1 := by
  have hp := insert_perm w xs
  have hlen := hp.length_eq
  have hsum := (hp.map (treeSize ∘ wordData)).sum_eq
  rw [listTree_size,listTree_size]
  simp only [List.length_cons,List.map_cons,List.sum_cons,Function.comp_def] at hlen hsum ⊢
  omega

theorem sort_size (xs : List W) :
    treeSize (listTree wordData (sort xs)) = treeSize (listTree wordData xs) := by
  have hp := sort_perm xs
  simp only [listTree_size,hp.length_eq,(hp.map (treeSize ∘ wordData)).sum_eq]

end MeanPayoff.TreeDevice.Sort
end

end OAI
