import OAI.Computability.MeanPayoff.Normalization

namespace OAI

section

end

section
namespace MeanPayoff.TreeDevice.Zip
open BinaryData
variable {α β γ : Type} (ea : α → Data) (eb : β → Data) (ec : γ → Data) (a : α) (b : β)

def restData := product (listTree ea) (listTree eb)
def stateData := StreamFold.stateData Median.unitData ec (restData ea eb)
def countData := listTree Median.unitData

variable {ea eb ec} {f : α × β → γ}
def zip (f : α × β → γ) (b : β) : List α → List β → List γ
  | [],_ => []
  | x::xs,ys => f (x,ys.headD b)::zip f b xs ys.tail

def row (f : α × β → γ) (a : α) (b : β) (p : Unit × (List α × List β)) : γ × (List α × List β) :=
  (f (p.2.1.headD a,p.2.2.headD b),(p.2.1.tail,p.2.2.tail))

noncomputable def localDevice : Device (product Median.unitData (restData ea eb)) (restData ea eb)
    (fun p : Unit × (List α × List β) => p.2) := second Median.unitData (restData ea eb)
noncomputable def leftDevice : Device (product Median.unitData (restData ea eb)) (listTree ea)
    (fun p : Unit × (List α × List β) => p.2.1) := compose localDevice (first (listTree ea) (listTree eb))
noncomputable def rightDevice : Device (product Median.unitData (restData ea eb)) (listTree eb)
    (fun p : Unit × (List α × List β) => p.2.2) := compose localDevice (second (listTree ea) (listTree eb))
noncomputable def headArgsDevice : Device (product Median.unitData (restData ea eb)) (product ea eb)
    (fun p : Unit × (List α × List β) => (p.2.1.headD a,p.2.2.headD b)) :=
  fanout (compose leftDevice (Head.device ea a)) (compose rightDevice (Head.device eb b))
noncomputable def tailsDevice : Device (product Median.unitData (restData ea eb)) (restData ea eb)
    (fun p : Unit × (List α × List β) => (p.2.1.tail,p.2.2.tail)) :=
  fanout (compose leftDevice (Tail.device ea)) (compose rightDevice (Tail.device eb))

variable (F : Device (product ea eb) ec f)
noncomputable def headDevice : Device (product Median.unitData (restData ea eb)) ec
    (fun p : Unit × (List α × List β) => f (p.2.1.headD a,p.2.2.headD b)) :=
  compose (headArgsDevice a b) F
noncomputable def rowDevice : Device (product Median.unitData (restData ea eb)) (product ec (restData ea eb)) (row f a b) :=
  fanout (headDevice a b F) tailsDevice

noncomputable def stateDevice : Device (restData ea eb) (stateData ea eb ec)
    (fun p : List α × List β => ((),([],p))) :=
  fanout (constant (restData ea eb) Median.unitData ()) (Lists.nilPrefix (restData ea eb) ec)
noncomputable def countDevice : Device (restData ea eb) countData
    (fun p : List α × List β => p.1.map (fun _ => ())) :=
  compose (first (listTree ea) (listTree eb)) (Map.device (constant ea Median.unitData ()))
noncomputable def initDevice : Device (restData ea eb) (product (stateData ea eb ec) countData)
    (fun p : List α × List β => (((),([],p)),p.1.map (fun _ => ()))) :=
  fanout stateDevice countDevice
noncomputable def resultDevice : Device (stateData ea eb ec) (listTree ec)
    (fun s : StreamFold.State Unit γ (List α × List β) => s.2.1.reverse) :=
  compose (compose (second Median.unitData (product (listTree ec) (restData ea eb)))
    (first (listTree ec) (restData ea eb))) (Lists.reverseDevice ec)
noncomputable def foldedDevice : Device (product (stateData ea eb ec) countData) (listTree ec)
    (fun z : StreamFold.State Unit γ (List α × List β) × Median.Count =>
      (Fold.fold (StreamFold.step (row f a b)) z.1 z.2).2.1.reverse) :=
  @compose (StreamFold.State Unit γ (List α × List β) × Median.Count)
    (StreamFold.State Unit γ (List α × List β)) (List γ)
    (product (stateData ea eb ec) countData) (stateData ea eb ec) (listTree ec)
    (fun z => Fold.fold (StreamFold.step (row f a b)) z.1 z.2) (fun s => s.2.1.reverse)
    (Fold.device (StreamFold.stepDevice (rowDevice a b F))) resultDevice
noncomputable def rawDevice : Device (restData ea eb) (listTree ec)
    (fun p : List α × List β =>
      (Fold.fold (StreamFold.step (row f a b)) ((),([],p)) (p.1.map (fun _ => ()))).2.1.reverse) :=
  compose initDevice (foldedDevice a b F)

theorem fold_exact (xs : List α) (ys : List β) (acc : List γ) :
    Fold.fold (StreamFold.step (row f a b)) ((),(acc,(xs,ys))) (List.replicate xs.length ()) =
      ((),((zip f b xs ys).reverse++acc,([],ys.drop xs.length))) := by
  induction xs generalizing ys acc with
  | nil => simp [Fold.fold,zip]
  | cons x xs ih =>
    simp only [List.length_cons,List.replicate_succ,Fold.fold,List.foldl_cons]
    change Fold.fold (StreamFold.step (row f a b))
      (StreamFold.step (row f a b) (((),(acc,(x::xs,ys))),())) (List.replicate xs.length ())=_
    simp only [StreamFold.step,row,List.headD_cons,List.tail_cons]
    rw [ih]
    simp [zip,List.reverse_cons,List.append_assoc,List.drop_tail]

noncomputable def device : Device (restData ea eb) (listTree ec) (fun p : List α × List β => zip f b p.1 p.2) :=
  (rawDevice a b F).extFun (by
    rintro ⟨xs,ys⟩
    change (Fold.fold (StreamFold.step (row f a b)) ((),([], (xs,ys)))
      (xs.map (fun _ => ()))).2.1.reverse = _
    rw [List.map_const, fold_exact]
    simp)

theorem length (xs : List α) (ys : List β) : (zip f b xs ys).length=xs.length := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => simp [zip,ih]

theorem ofFn {n : ℕ} (x : Fin n → α) (y : Fin n → β) :
    zip f b (List.ofFn x) (List.ofFn y) = List.ofFn (fun i => f (x i,y i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.ofFn_succ,zip,List.headD_cons,List.tail_cons] using congrArg (List.cons (f (x 0,y 0))) (ih (fun i => x i.succ) (fun i => y i.succ))

theorem local_linear : LinearCost (localDevice (ea:=ea) (eb:=eb)) := LinearCost.second _ _
theorem left_linear : LinearCost (leftDevice (ea:=ea) (eb:=eb)) := LinearCost.compose local_linear (LinearCost.first _ _)
theorem right_linear : LinearCost (rightDevice (ea:=ea) (eb:=eb)) := LinearCost.compose local_linear (LinearCost.second _ _)
theorem headArgs_linear : LinearCost (headArgsDevice (ea:=ea) (eb:=eb) a b) :=
  LinearCost.fanout (LinearCost.compose left_linear (LinearCost.head _ _)) (LinearCost.compose right_linear (LinearCost.head _ _))
theorem tails_linear : LinearCost (tailsDevice (ea:=ea) (eb:=eb)) :=
  LinearCost.fanout (LinearCost.compose left_linear (LinearCost.tail _)) (LinearCost.compose right_linear (LinearCost.tail _))
theorem head_polynomial (hF : PolynomialCost F) : PolynomialCost (headDevice a b F) := PolynomialCost.compose (headArgs_linear a b).polynomial hF
theorem row_polynomial (hF : PolynomialCost F) : PolynomialCost (rowDevice a b F) := PolynomialCost.fanout (head_polynomial a b F hF) tails_linear.polynomial

theorem fold_polynomial (hF : PolynomialCost F) : PolynomialCost (Fold.device (StreamFold.stepDevice (rowDevice a b F))) := by
  apply StreamFold.polynomial _ (row_polynomial a b F hF)
  intro u r
  have hl : treeSize (listTree ea r.1.tail)≤treeSize (listTree ea r.1) := by
    rcases r with ⟨xs,ys⟩; cases xs <;> simp only [List.tail_nil,List.tail_cons,listTree,treeSize_pair] <;> omega
  have hr : treeSize (listTree eb r.2.tail)≤treeSize (listTree eb r.2) := by
    rcases r with ⟨xs,ys⟩; cases ys <;> simp only [List.tail_nil,List.tail_cons,listTree,treeSize_pair] <;> omega
  simp only [row,restData,product,treeSize_pair]
  omega

theorem state_linear : LinearCost (stateDevice (ea:=ea) (eb:=eb) (ec:=ec)) := LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.nilPrefix _ _)
theorem count_polynomial : PolynomialCost (countDevice (ea:=ea) (eb:=eb)) :=
  PolynomialCost.compose (LinearCost.first _ _).polynomial (PolynomialCost.map (LinearCost.constant _ _ _).polynomial)
theorem init_polynomial : PolynomialCost (initDevice (ea:=ea) (eb:=eb) (ec:=ec)) := PolynomialCost.fanout state_linear.polynomial count_polynomial
theorem result_polynomial : PolynomialCost (resultDevice (ea:=ea) (eb:=eb) (ec:=ec)) :=
  PolynomialCost.compose (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)).polynomial (PolynomialCost.reverse _)
theorem folded_polynomial (hF : PolynomialCost F) : PolynomialCost (foldedDevice a b F) := PolynomialCost.compose (fold_polynomial a b F hF) result_polynomial
theorem raw_polynomial (hF : PolynomialCost F) : PolynomialCost (rawDevice a b F) := PolynomialCost.compose init_polynomial (folded_polynomial a b F hF)
theorem polynomial (hF : PolynomialCost F) : PolynomialCost (device a b F) := raw_polynomial a b F hF
end MeanPayoff.TreeDevice.Zip
namespace MeanPayoff.TreeDevice.Certified
open BinaryData

class Encoding (α : Type) where
  encode : α → Data
export Encoding (encode)

instance : Encoding Unit := ⟨Median.unitData⟩
instance : Encoding Bool := ⟨Compare.bitTree⟩
instance : Encoding SignedBits.Word := ⟨wordData⟩
instance {α β : Type} [Encoding α] [Encoding β] : Encoding (α × β) :=
  ⟨product encode encode⟩
instance {α : Type} [Encoding α] : Encoding (List α) := ⟨listTree encode⟩

structure Code (α β : Type) [Encoding α] [Encoding β] where
  eval : α → β
  device : Device encode encode eval
  polynomial : PolynomialCost device

namespace Code
variable {α β γ δ : Type} [Encoding α] [Encoding β] [Encoding γ] [Encoding δ]
instance : CoeFun (Code α β) (fun _ => α → β) := ⟨Code.eval⟩

noncomputable def id : Code α α := ⟨_root_.id, identity encode, (LinearCost.identity _).polynomial⟩
noncomputable def const (b : β) : Code α β :=
  ⟨fun _ => b, constant encode encode b, (LinearCost.constant _ _ _).polynomial⟩
noncomputable def comp (f : Code α β) (g : Code β γ) : Code α γ :=
  ⟨g.eval ∘ f.eval, compose f.device g.device, PolynomialCost.compose f.polynomial g.polynomial⟩
noncomputable def pair (f : Code α β) (g : Code α γ) : Code α (β × γ) :=
  ⟨fun x => (f x,g x), fanout f.device g.device, PolynomialCost.fanout f.polynomial g.polynomial⟩
noncomputable def fst : Code (α × β) α :=
  ⟨Prod.fst, first encode encode, (LinearCost.first _ _).polynomial⟩
noncomputable def snd : Code (α × β) β :=
  ⟨Prod.snd, second encode encode, (LinearCost.second _ _).polynomial⟩
noncomputable def branch (p : Code α Bool) (f g : Code α β) : Code α β :=
  ⟨fun x => if p x then f x else g x, TreeDevice.branch p.device f.device g.device,
    PolynomialCost.branch p.polynomial f.polynomial g.polynomial⟩
noncomputable def map (f : Code α β) : Code (List α) (List β) :=
  ⟨List.map f.eval, Map.device f.device, PolynomialCost.map f.polynomial⟩
noncomputable def envMap (f : Code (α × β) γ) : Code (α × List β) (List γ) :=
  ⟨fun z => z.2.map (fun x => f (z.1,x)), EnvMap.device f.device, EnvMap.polynomial f.polynomial⟩
noncomputable def head (a : α) : Code (List α) α :=
  ⟨fun xs => xs.headD a, Head.device encode a, (LinearCost.head _ _).polynomial⟩
noncomputable def tail : Code (List α) (List α) :=
  ⟨List.tail, Tail.device encode, (LinearCost.tail _).polynomial⟩
noncomputable def cons : Code (α × List α) (List α) :=
  ⟨fun z => z.1::z.2, Lists.consDevice encode, (LinearCost.cons _).polynomial⟩
noncomputable def reverse : Code (List α) (List α) :=
  ⟨List.reverse, Lists.reverseDevice encode, PolynomialCost.reverse _⟩
noncomputable def zip (a : α) (b : β) (f : Code (α × β) γ) : Code (List α × List β) (List γ) :=
  ⟨fun z => Zip.zip f.eval b z.1 z.2, Zip.device a b f.device, Zip.polynomial a b f.device f.polynomial⟩
noncomputable def fold (f : Code (α × β) α)
    (hg : ∀ a b, treeSize (encode (f (a,b))) ≤ treeSize (encode a)+treeSize (encode b)+1) :
    Code (α × List β) α :=
  ⟨fun z => Fold.fold f.eval z.1 z.2, Fold.device f.device, Fold.polynomial f.polynomial hg⟩

noncomputable def recode (f : Code α β) (i : γ → α) (g : γ → δ)
    (hi : ∀ x, encode (i x)=encode x) (ho : ∀ x, encode (f (i x))=encode (g x)) : Code γ δ := by
  refine ⟨g,f.device.recode encode encode i g hi ho,?_⟩
  obtain ⟨K,d,h⟩ := f.polynomial
  refine ⟨K,d,fun x => ?_⟩
  change f.device.limit (i x) ≤ _
  simpa only [hi x] using h (i x)
noncomputable def foldPrefix (f : Code (α × β) α) (B e : ℕ)
    (hb : ∀ (a : α) (xs : List β) (k : ℕ), k≤xs.length → treeSize (encode (Fold.fold f.eval a (xs.take k))) ≤
      B*(treeSize (encode (a,xs))+1)^e) : Code (α × List β) α :=
  ⟨fun z => Fold.fold f.eval z.1 z.2,Fold.device f.device,Fold.polynomial_of_prefix f.polynomial B e hb⟩

def ext (f : Code α β) (g : α → β) (h : ∀ x, f x = g x) : Code α β :=
  ⟨g,f.device.extFun h,f.polynomial⟩

@[simp] theorem id_eval (x : α) : (id : Code α α) x=x := rfl
@[simp] theorem const_eval (b : β) (x : α) : (const b : Code α β) x=b := rfl
@[simp] theorem comp_eval (f : Code α β) (g : Code β γ) (x : α) : comp f g x=g (f x) := rfl
@[simp] theorem pair_eval (f : Code α β) (g : Code α γ) (x : α) : pair f g x=(f x,g x) := rfl
@[simp] theorem fst_eval (x : α × β) : (fst : Code (α × β) α) x=x.1 := rfl
@[simp] theorem snd_eval (x : α × β) : (snd : Code (α × β) β) x=x.2 := rfl
@[simp] theorem branch_eval (p : Code α Bool) (f g : Code α β) (x : α) : branch p f g x=(if p x then f x else g x) := rfl
@[simp] theorem map_eval (f : Code α β) (xs : List α) : map f xs=xs.map f.eval := rfl
@[simp] theorem envMap_eval (f : Code (α × β) γ) (z : α × List β) : envMap f z=z.2.map (fun x => f (z.1,x)) := rfl
@[simp] theorem head_eval (a : α) (xs : List α) : head a xs=xs.headD a := rfl
@[simp] theorem tail_eval (xs : List α) : tail xs=xs.tail := rfl
@[simp] theorem cons_eval (z : α × List α) : cons z=z.1::z.2 := rfl
@[simp] theorem reverse_eval (xs : List α) : reverse xs=xs.reverse := rfl
@[simp] theorem zip_eval (a : α) (b : β) (f : Code (α × β) γ) (z : List α × List β) : zip a b f z=Zip.zip f.eval b z.1 z.2 := rfl
@[simp] theorem ext_eval (f : Code α β) (g : α → β) (h : ∀ x, f x=g x) (x : α) : ext f g h x=g x := rfl
end Code
end MeanPayoff.TreeDevice.Certified
namespace MeanPayoff.TreeDevice.Certified
open BinaryData
open Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
abbrev W := SignedBits.Word
abbrev Count := List Unit

namespace Code
variable {α β : Type} [Encoding α] [Encoding β]
noncomputable def swap : Code (α × β) (β × α) := snd ⋏ₚ fst
noncomputable def count : Code (List α) Count := map (const ())
noncomputable def not : Code Bool Bool := ⟨Bool.not,Bits.notDevice,LinearCost.not.polynomial⟩
noncomputable def and : Code (Bool × Bool) Bool := branch fst snd (const false)
noncomputable def or : Code (Bool × Bool) Bool := branch fst (const true) snd
noncomputable def empty : Code (List α) Bool :=
  count ≫ₚ (⟨List.isEmpty,CountTest.emptyDevice,CountTest.empty_polynomial⟩ : Code Count Bool)
noncomputable def drop : Code (List α × Count) (List α) :=
  ⟨fun z => z.1.drop z.2.length,Median.dropDevice encode,Median.drop_polynomial _⟩
noncomputable def nth (a : α) : Code (List α × Count) α := drop ≫ₚ head a

theorem list_size_append (xs ys : List α) :
    treeSize (encode (xs++ys))+1=treeSize (encode xs)+treeSize (encode ys) := by
  change treeSize (listTree encode (xs++ys))+1=treeSize (listTree encode xs)+treeSize (listTree encode ys)
  simp only [listTree_size,List.length_append,List.map_append,List.sum_append]
  omega

noncomputable def consAcc : Code (List α × α) (List α) := swap ≫ₚ cons
noncomputable def revAppend : Code (List α × List α) (List α) :=
  fold consAcc (by
    intro xs x
    change treeSize (listTree encode (x::xs)) ≤ treeSize (listTree encode xs)+treeSize (encode x)+1
    rw [listTree,treeSize_pair]
    omega)
noncomputable def append : Code (List α × List α) (List α) :=
  (snd ⋏ₚ (fst ≫ₚ reverse)) ≫ₚ revAppend

theorem revAppend_eval (z : List α × List α) : revAppend z=z.2.reverse++z.1 := by
  change z.2.foldl (fun xs x => x::xs) z.1 = _
  exact List.foldl_flip_cons_eq_append'
@[simp] theorem append_eval (z : List α × List α) : append z=z.1++z.2 := by
  simp only [append,comp_eval,pair_eval,snd_eval,fst_eval,reverse_eval,revAppend_eval,List.reverse_reverse]

noncomputable def flatten : Code (List (List α)) (List α) :=
  (const [] ⋏ₚ Code.id) ≫ₚ fold append (by
    intro xs ys
    have h := list_size_append xs ys
    rw [append_eval]
    dsimp only at *
    omega)
@[simp] theorem flatten_eval (xss : List (List α)) : flatten xss=xss.flatten := by
  change xss.foldl (fun xs ys => append (xs,ys)) [] = _
  simp only [append_eval]
  simpa using (List.foldl_append_eq_append (l:=xss) (f:=_root_.id) (l':=[]))

noncomputable def filter (p : Code α Bool) : Code (List α) (List α) := by
  let q : Code (Unit × α) Bool := snd ≫ₚ p
  let f : Code (Unit × List α) (List α) :=
    ⟨fun z => z.2.filter (fun x => q (z.1,x)),EnvFilter.device q.device,EnvFilter.polynomial q.polynomial⟩
  exact (const () ⋏ₚ Code.id) ≫ₚ f
@[simp] theorem filter_eval (p : Code α Bool) (xs : List α) : filter p xs=xs.filter p.eval := rfl

noncomputable def any (p : Code α Bool) : Code (List α) Bool :=
  filter p ≫ₚ empty ≫ₚ not
@[simp] theorem empty_eval (xs : List α) : empty xs=xs.isEmpty := by
  cases xs <;> rfl
@[simp] theorem count_eval (xs : List α) : count xs=xs.map (fun _ => ()) := rfl
@[simp] theorem not_eval (b : Bool) : not b= !b := rfl
@[simp] theorem nth_eval (a : α) (z : List α × Count) : nth a z=z.1.getD z.2.length a := by
  change (z.1.drop z.2.length).headD a=z.1.getD z.2.length a
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
end Code

structure Digits where
  bits : List Bool
instance : Encoding Digits := ⟨fun d => listTree boolData d.bits⟩

namespace Word
noncomputable def add : Code (W × W) W :=
  ⟨Add.sumPair,Add.device,LinearCost.add.polynomial⟩
noncomputable def neg : Code W W := ⟨Negate.negate,Negate.device,Negate.polynomial⟩
noncomputable def sub : Code (W × W) W := (fst ⋏ₚ (snd ≫ₚ neg)) ≫ₚ add
noncomputable def lt : Code (W × W) Bool :=
  ⟨Compare.testPair,Compare.device,LinearCost.compare.polynomial⟩
noncomputable def le : Code (W × W) Bool := Code.swap ≫ₚ lt ≫ₚ Code.not
noncomputable def min : Code (W × W) W := ⟨Order.low,Order.minDevice,LinearCost.min.polynomial⟩
noncomputable def max : Code (W × W) W := ⟨Order.high,Order.maxDevice,LinearCost.max.polynomial⟩
noncomputable def half : Code W W := by
  let P := pairMap (identity boolData) (Tail.device boolData)
  let hP := LinearCost.pairMap (LinearCost.identity boolData) (LinearCost.tail boolData)
  let hin : ∀ w : W, product boolData (listTree boolData) (w.sign,w.digits)=wordData w := by
    intro w
    simp only [product,wordData,listData,Halve.listTree_boolData]
  let F := P.recode wordData wordData (fun w : W => (w.sign,w.digits)) Halve.halve hin (by
    intro w
    simp only [product,wordData,listData,Halve.halve,Halve.listTree_boolData]
    rfl)
  exact ⟨Halve.halve,F,(LinearCost.recode hP _ _ _ _ _ _).polynomial⟩
noncomputable def double : Code W W := ⟨Multiply.double,Multiply.doubleDevice,Multiply.double_linear.polynomial⟩
noncomputable def average : Code (W × W) W := add ≫ₚ half
noncomputable def signDevice : Device wordData Compare.bitTree SignedBits.Word.sign :=
  (compose (Head.device boolData false) Multiply.rawTest).recode wordData Compare.bitTree
    (fun w => w.sign::w.digits) SignedBits.Word.sign
    (by intro w; exact Halve.listTree_boolData _) (by intro w; rfl)
noncomputable def sign : Code W Bool :=
  ⟨SignedBits.Word.sign, signDevice,
    (LinearCost.recode (LinearCost.compose (LinearCost.head _ _) Multiply.rawTest_linear) _ _ _ _ _ _).polynomial⟩
noncomputable def digitsDevice : Device wordData encode (fun w : W => Digits.mk w.digits) :=
  (Tail.device boolData).recode wordData encode (fun w => w.sign::w.digits)
    (fun w => Digits.mk w.digits) (by intro w; exact Halve.listTree_boolData _) (by intro w; rfl)
noncomputable def digits : Code W Digits :=
  ⟨fun w => ⟨w.digits⟩,digitsDevice,(LinearCost.recode (LinearCost.tail _) _ _ _ _ _ _).polynomial⟩
noncomputable def mulDigitsDevice : Device encode wordData (fun z : W × Digits => Multiply.multiply (z.1,z.2.bits)) :=
  Multiply.device.recode encode wordData (fun z : W × Digits => (z.1,z.2.bits))
    (fun z : W × Digits => Multiply.multiply (z.1,z.2.bits)) (by intro z; rfl) (by intro z; rfl)
noncomputable def mulDigits : Code (W × Digits) W := by
  refine ⟨fun z => Multiply.multiply (z.1,z.2.bits),mulDigitsDevice,?_⟩
  obtain ⟨K,d,h⟩ := Multiply.polynomial
  exact ⟨K,d,fun z => h (z.1,z.2.bits)⟩
noncomputable def unsignedMul : Code (W × W) W := (fst ⋏ₚ (snd ≫ₚ digits)) ≫ₚ mulDigits
noncomputable def mul : Code (W × W) W :=
  Code.branch (snd ≫ₚ sign) (((fst ⋏ₚ (snd ≫ₚ neg)) ≫ₚ unsignedMul) ≫ₚ neg) unsignedMul

@[simp] theorem add_val (x y : W) : (add (x,y)).val=x.val+y.val := Add.sumPair_val _
@[simp] theorem neg_val (x : W) : (neg x).val= -x.val := Negate.exact x
@[simp] theorem sub_val (x y : W) : (sub (x,y)).val=x.val-y.val := by simp [sub,sub_eq_add_neg]
@[simp] theorem lt_eval (x y : W) : lt (x,y)=decide (x.val<y.val) := Compare.testPair_eq _
@[simp] theorem le_eval (x y : W) : le (x,y)=decide (x.val≤y.val) := by
  simp only [le,Code.swap,comp_eval,pair_eval,snd_eval,fst_eval,lt_eval,not_eval]
  rw [← decide_not]
  exact decide_eq_decide.mpr not_lt
@[simp] theorem min_val (x y : W) : (min (x,y)).val=Min.min x.val y.val := Order.low_val _
@[simp] theorem max_val (x y : W) : (max (x,y)).val=Max.max x.val y.val := Order.high_val _
@[simp] theorem half_val (x : W) : (half x).val=x.val/2 := Halve.halve_val _
@[simp] theorem double_val (x : W) : (double x).val=2*x.val := Multiply.double_val _
@[simp] theorem average_val (x y : W) : (average (x,y)).val=(x.val+y.val)/2 := by simp [average]
@[simp] theorem sign_eval (x : W) : sign x=x.sign := rfl
@[simp] theorem unsignedMul_val (x y : W) (hy : y.sign=false) : (unsignedMul (x,y)).val=x.val*y.val := by
  change (Multiply.multiply (x,y.digits)).val=x.val*y.val
  rw [Multiply.exact]
  simp [SignedBits.Word.val,hy]
@[simp] theorem mul_val (x y : W) : (mul (x,y)).val=x.val*y.val := by
  change (if y.sign then neg (unsignedMul (x,neg y)) else unsignedMul (x,y)).val=x.val*y.val
  by_cases h : y.sign=true
  · rw [ite_eq_left h]
    have hn : (neg y).sign=false := by
      have hy : y.val<0 := (SignedBits.val_negative y).mpr h
      have hp : ¬(neg y).val<0 := by rw [neg_val]; omega
      have := mt (SignedBits.val_negative (neg y)).mpr hp
      cases hs : (neg y).sign <;> simp_all
    simp only [neg_val,unsignedMul_val _ _ hn]
    ring
  · rw [ite_eq_right h]
    have hy : y.sign=false := Bool.eq_false_iff.mpr h
    exact unsignedMul_val x y hy
end Word
end MeanPayoff.TreeDevice.Certified
end

end OAI
