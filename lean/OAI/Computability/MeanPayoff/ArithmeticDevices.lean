import OAI.Computability.MeanPayoff.Sorting

namespace OAI

section
namespace MeanPayoff.TreeDevice.Forest
open RegisterBits BinaryData

def atom {α : Type} (a : α → List Data) :
    Segment (fun z => ⟨a z,[],[]⟩) (fun z => ⟨Data.nil::a z,[],[]⟩) where
  program := bitOp 0 (.push false)
  limit _ := 2
  correct z suffix out bits := by
    rw [bitOp_runs]
    simp only [stack,encode_cons,encode_nil,BinaryData.encode,List.cons_append,core_zero,BinaryStack.applyOp]
    apply Take.config_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl

noncomputable def literal {α : Type} (t : Data) (a : α → List Data) :
    Segment (fun z => ⟨a z,[],[]⟩) (fun z => ⟨t::a z,[],[]⟩) :=
  match t with
  | .nil => atom a
  | .pair u v => (literal v a).seq ((literal u (fun z => v::a z)).seq
      (pair (fun _ => u) (fun _ => v) a (fun _ => []) (fun _ => [])))

end MeanPayoff.TreeDevice.Forest
namespace MeanPayoff.TreeDevice
open BinaryData

noncomputable def constant {α β : Type} (ea : α → Data) (eb : β → Data) (b : β) :
    Device ea eb (fun _ => b) :=
  Forest.toDevice _ _ _ ((Forest.drop ea (fun _ => [])).seq (Forest.literal (eb b) (fun _ => [])))

noncomputable def branch {α β : Type} {ea : α → Data} {eb : β → Data}
    {test : α → Bool} {f g : α → β} (T : Device ea Compare.bitTree test)
    (F : Device ea eb f) (G : Device ea eb g) : Device ea eb (fun a => if test a then f a else g a) :=
  compose (fanout T (fanout F G)) (Select.device eb)

namespace Bits

noncomputable def notDevice : Device Compare.bitTree Compare.bitTree Bool.not :=
  (branch (identity Compare.bitTree) (constant Compare.bitTree Compare.bitTree false)
    (constant Compare.bitTree Compare.bitTree true)).extFun (by intro b; cases b <;> rfl)

end Bits
namespace Head
open RegisterBits

noncomputable abbrev flow {α : Type} (ea : α → Data) (a : α) : Flow.Program 5 where
  nodes := 3
  start := 0
  block := ![skip,(first ea (listTree ea)).program,(constant (listTree ea) ea a).program]
  read _ := 0
  next p top _ := if p=0 then some ⟨if top=some true then 1 else 2,.keep,none⟩ else none

noncomputable abbrev program {α : Type} (ea : α → Data) (a : α) := Flow.compile (flow ea a)

noncomputable def limit {α : Type} (ea : α → Data) (a : α) : List α → ℕ
  | [] => (constant (listTree ea) ea a).limit []+3
  | x::xs => (first ea (listTree ea)).limit (x,xs)+3

theorem runs {α : Type} (ea : α → Data) (a : α) (xs : List α) (suffix out : List Bool) :
    Reaches (program ea a) ⟨some (program ea a).start,store (listTree ea xs) suffix,out⟩
      ⟨none,store (ea (xs.headD a)) suffix,out⟩ (limit ea a xs) := by
  cases xs with
  | nil =>
    have h₀ : Reaches (program ea a)
        (Flow.state (flow ea a) 0 (store (listTree ea []) suffix) out)
        (Flow.state (flow ea a) 2 (store (listTree ea []) suffix) out) 2 := by
      intro bits
      apply Flow.hop_update (flow ea a) 0 2 _ _ _ out bits 1 .keep rfl (by intros; rfl)
      simp only [BinaryStack.applyOp,Function.update_eq_self,advance]
    have h₁ : Reaches (program ea a)
        (Flow.state (flow ea a) 2 (store (listTree ea []) suffix) out)
        ⟨none,store (ea a) suffix,out⟩ ((constant (listTree ea) ea a).limit []+1) := by
      intro bits
      exact Flow.finish (flow ea a) 2 _ _ out bits _
        ((constant (listTree ea) ea a).correct [] suffix out bits) (by intros; rfl)
    exact (h₀.trans h₁).mono (by dsimp only [limit]; omega)
  | cons x xs =>
    have h₀ : Reaches (program ea a)
        (Flow.state (flow ea a) 0 (store (listTree ea (x::xs)) suffix) out)
        (Flow.state (flow ea a) 1 (store (listTree ea (x::xs)) suffix) out) 2 := by
      intro bits
      apply Flow.hop_update (flow ea a) 0 1 _ _ _ out bits 1 .keep rfl (by intros; rfl)
      simp only [BinaryStack.applyOp,Function.update_eq_self,advance]
    have h₁ : Reaches (program ea a)
        (Flow.state (flow ea a) 1 (store (listTree ea (x::xs)) suffix) out)
        ⟨none,store (ea x) suffix,out⟩ ((first ea (listTree ea)).limit (x,xs)+1) := by
      intro bits
      exact Flow.finish (flow ea a) 1 _ _ out bits _
        ((first ea (listTree ea)).correct (x,xs) suffix out bits) (by intros; rfl)
    exact (h₀.trans h₁).mono (by dsimp only [limit]; omega)

noncomputable def device {α : Type} (ea : α → Data) (a : α) :
    Device (listTree ea) ea (fun xs => xs.headD a) :=
  ofProgram _ _ _ (program ea a) (limit ea a)
    (fun xs suffix out bits => (runs ea a xs suffix out).pad rfl bits)

end Head
end MeanPayoff.TreeDevice
namespace MeanPayoff.TreeDevice.Median
open BinaryData

abbrev Count := List Unit
abbrev State := Bool × Count

def unitData (_ : Unit) : Data := .nil
def stateData := product Compare.bitTree (listTree unitData)

def halfStep (s : State) : State := (!s.1, if s.1 then ()::s.2 else s.2)

noncomputable def incrementDevice : Device (listTree unitData) (listTree unitData) (fun xs => ()::xs) := by
  let P := compose (fanout (constant (listTree unitData) unitData ()) (identity (listTree unitData)))
    (Lists.consDevice unitData)
  exact P.extFun (by intro xs; rfl)

noncomputable def halfStepDevice : Device stateData stateData halfStep :=
  fanout (compose (first Compare.bitTree (listTree unitData)) Bits.notDevice)
    (branch (first Compare.bitTree (listTree unitData))
      (compose (second Compare.bitTree (listTree unitData)) incrementDevice)
      (second Compare.bitTree (listTree unitData)))

def count {α : Type} (xs : List α) : Count :=
  (xs.foldl (fun s _ => halfStep s) (false,[])).2

noncomputable def countDevice {α : Type} (ea : α → Data) : Device (listTree ea) (listTree unitData) count := by
  let F := compose (first stateData ea) halfStepDevice
  let P := compose (fanout (constant (listTree ea) stateData (false,[])) (identity (listTree ea)))
    (compose (Fold.device F) (second Compare.bitTree (listTree unitData)))
  exact P.extFun (by intro xs; rfl)

theorem halfStep_measure (s : State) :
    2*(halfStep s).2.length+(halfStep s).1.toNat = 2*s.2.length+s.1.toNat+1 := by
  rcases s with ⟨b,c⟩
  cases b <;> simp [halfStep] ; omega

theorem count_measure {α : Type} (xs : List α) (s : State) :
    let t := xs.foldl (fun s _ => halfStep s) s
    2*t.2.length+t.1.toNat = 2*s.2.length+s.1.toNat+xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.length_cons]
    rw [ih,halfStep_measure]
    omega

theorem count_length {α : Type} (xs : List α) : (count xs).length = xs.length/2 := by
  have h := count_measure xs (false,[])
  have hb : (xs.foldl (fun s _ => halfStep s) (false,[])).1.toNat ≤ 1 := by
    cases (xs.foldl (fun s _ => halfStep s) (false,[])).1 <;> decide
  dsimp only at h
  simp only [List.length_nil,Bool.toNat_false] at h
  unfold count
  omega

theorem repeatTail {α : Type} (xs : List α) (ns : Count) :
    Fold.fold (fun z : List α × Unit => z.1.tail) xs ns = xs.drop ns.length := by
  induction ns generalizing xs with
  | nil => simp [Fold.fold]
  | cons u ns ih =>
    change Fold.fold (fun z : List α × Unit => z.1.tail) xs.tail ns = _
    rw [ih]
    simpa only [List.length_cons] using (List.drop_tail (l := xs) (i := ns.length))

noncomputable def dropDevice {α : Type} (ea : α → Data) :
    Device (product (listTree ea) (listTree unitData)) (listTree ea)
      (fun z : List α × Count => z.1.drop z.2.length) :=
  (Fold.device (compose (first (listTree ea) unitData) (Tail.device ea))).extFun (by
    intro z
    exact repeatTail _ _)

def zeroWord : SignedBits.Word := ⟨false,[]⟩

def median (xs : List SignedBits.Word) : SignedBits.Word :=
  ((Sort.sort xs).drop (count xs).length).headD zeroWord

noncomputable def device : Device (listTree wordData) wordData median :=
  compose (fanout Sort.sortDevice (countDevice wordData))
    (compose (dropDevice wordData) (Head.device wordData zeroWord))

end MeanPayoff.TreeDevice.Median
namespace MeanPayoff.TreeDevice.Median
open BinaryData

theorem val_headD (xs : List SignedBits.Word) (w : SignedBits.Word) :
    (xs.headD w).val = (xs.map SignedBits.Word.val).headD w.val := by
  cases xs <;> rfl

@[simp] theorem zeroWord_val : zeroWord.val = 0 := rfl

theorem value_exact (xs : List SignedBits.Word) :
    (median xs).val = medianInt (xs.map SignedBits.Word.val) := by
  rw [median,count_length,val_headD,List.map_drop,Sort.sort_values,zeroWord_val]
  by_cases h : xs.length=0
  · have hx : xs=[] := List.length_eq_zero_iff.mp h
    subst xs
    simp [medianInt]
  · have hp : 0 < (xs.map SignedBits.Word.val).length := by simp; omega
    have hi : xs.length/2 < ((xs.map SignedBits.Word.val).mergeSort (· ≤ ·)).length := by
      simp only [List.length_mergeSort,List.length_map]
      exact Nat.div_lt_self (by omega) (by omega)
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
    have hpos : 0 < xs.length := by omega
    simp only [medianInt,List.length_map,dite_eq_left hpos]

noncomputable def vectorDevice :
    Device (listTree (listTree wordData)) (listTree wordData) (List.map median) := Map.device device

theorem coordinate_exact {n : ℕ} (batches : Fin n → List SignedBits.Word)
    (as : List (Fin n → ℤ))
    (hb : ∀ i, (batches i).map SignedBits.Word.val = as.map (fun p => p i)) :
    (fun i => (median (batches i)).val) = MeanPayoff.median as := by
  funext i
  rw [value_exact,hb]
  rfl

end MeanPayoff.TreeDevice.Median
namespace MeanPayoff.TreeDevice
open BinaryData

def LinearCost {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : Prop := ∃ K : ℕ, ∀ x, F.limit x ≤ K*(treeSize (ea x)+1)

namespace LinearCost

theorem identity {α : Type} (ea : α → Data) : LinearCost (TreeDevice.identity ea) := by
  refine ⟨1,?_⟩
  intro x
  simp only [TreeDevice.identity,Nat.one_mul]
  omega

theorem compose {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} {F : Device ea eb f} {G : Device eb ec g}
    (hF : LinearCost F) (hG : LinearCost G) : LinearCost (TreeDevice.compose F G) := by
  obtain ⟨K,hK⟩ := hF
  obtain ⟨M,hM⟩ := hG
  refine ⟨K+M*(K+2)+2,?_⟩
  intro x
  have h₁ := hK x
  have h₂ := hM (f x)
  have hi := TreeDevice.output_size F x
  have hb : treeSize (eb (f x))+1 ≤ (K+2)*(treeSize (ea x)+1) := by nlinarith
  have hm := Nat.mul_le_mul_left M hb
  rw [compose_limit]
  nlinarith

theorem dup {α : Type} (ea : α → Data) : LinearCost (TreeDevice.dup ea) := by
  refine ⟨13,?_⟩
  intro x
  rw [dup_limit]
  omega

theorem pairMap {α β γ δ : Type} {ea : α → Data} {eb : β → Data}
    {ec : γ → Data} {ed : δ → Data} {f : α → β} {g : γ → δ}
    {F : Device ea eb f} {G : Device ec ed g} (hF : LinearCost F) (hG : LinearCost G) :
    LinearCost (TreeDevice.pairMap F G) := by
  obtain ⟨K,hK⟩ := hF
  obtain ⟨M,hM⟩ := hG
  refine ⟨25*K+13*M+100,?_⟩
  rintro ⟨x,y⟩
  have h₁ : F.limit x ≤ K*(treeSize (ea x)+treeSize (ec y)+2) :=
    (hK x).trans (Nat.mul_le_mul_left K (by omega))
  have h₂ : G.limit y ≤ M*(treeSize (ea x)+treeSize (ec y)+2) :=
    (hM y).trans (Nat.mul_le_mul_left M (by omega))
  have hi := TreeDevice.output_size F x
  have hj := TreeDevice.output_size G y
  rw [pairMap_limit]
  simp only [product,treeSize_pair]
  nlinarith

theorem fanout {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : α → γ} {F : Device ea eb f} {G : Device ea ec g}
    (hF : LinearCost F) (hG : LinearCost G) : LinearCost (TreeDevice.fanout F G) :=
  compose (dup ea) (pairMap hF hG)

theorem first {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (TreeDevice.first ea eb) := by
  refine ⟨30,?_⟩
  rintro ⟨x,y⟩
  rw [first_limit]
  simp only [product,treeSize_pair]
  omega

theorem second {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (TreeDevice.second ea eb) := by
  refine ⟨10,?_⟩
  rintro ⟨x,y⟩
  rw [second_limit]
  simp only [product,treeSize_pair]
  omega

theorem select {α : Type} (ea : α → Data) : LinearCost (Select.device ea) := by
  refine ⟨43,?_⟩
  rintro ⟨b,x,y⟩
  have h := Select.limit_le ea (b,x,y)
  dsimp only at h
  change Select.limit ea (b,x,y) ≤ _
  simp only [product,treeSize_pair]
  omega

theorem compare : LinearCost Compare.device := by
  refine ⟨100,?_⟩
  intro z
  have h := Compare.limit_le z
  have h₁ := digits_le_wordSize z.1
  have h₂ := digits_le_wordSize z.2
  change Compare.limit z ≤ _
  simp only [Compare.pairWord,treeSize_pair]
  omega

theorem add : LinearCost Add.device := by
  refine ⟨100,?_⟩
  intro z
  have h₁ := digits_le_wordSize z.1
  have h₂ := digits_le_wordSize z.2
  have ho := wordSize_bound (Add.sumPair z)
  have hl := SignedBits.add_length z.1.sign z.2.sign false z.1.digits z.2.digits
  change (Add.sumPair z).digits.length = _ at hl
  change Add.limit z ≤ _
  simp only [Add.limit,Add.pairWord,treeSize_pair]
  rw [hl] at ho
  omega

theorem min : LinearCost Order.minDevice :=
  compose (fanout compare (identity _)) (select _)

theorem max : LinearCost Order.maxDevice :=
  compose (fanout compare (fanout (second _ _) (first _ _))) (select _)

end LinearCost
end MeanPayoff.TreeDevice
end

end OAI
