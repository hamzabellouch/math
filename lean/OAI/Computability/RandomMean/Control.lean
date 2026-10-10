import OAI.Computability.RandomMean.Orientation

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Code
variable {α β : Type} [Encoding α] [Encoding β]
end Code

namespace RawControl
abbrev Orient := RawOrientation.Data
abbrev Tuple := RawBudget.Data×RawBox.Data×Count×List W×List W×List (List W)×Orient×List Orient
structure Pack where
  p : RawBudget.Data
  b : RawBox.Data
  t : Count
  q : List W
  r : List W
  vs : List (List W)
  o : Orient
  os : List Orient

def Pack.tuple (z : Pack) : Tuple := (z.p,z.b,z.t,z.q,z.r,z.vs,z.o,z.os)
instance : Encoding Pack := ⟨fun z => encode z.tuple⟩

def zeroBudget : RawBudget.Data := ((Array.zero,Array.zero),(Array.zero,Array.zero),[],[])
def zeroBox : RawBox.Data := (Array.zero,[],[])
def Pack.zero : Pack := ⟨zeroBudget,zeroBox,[],[],[],[],(false,[]),[]⟩

noncomputable def proj {α : Type} [Encoding α] (f : Code Tuple α) : Code Pack α :=
  f.recode Pack.tuple (fun z => f z.tuple) (fun _ => rfl) (fun _ => rfl)
noncomputable def p : Code Pack RawBudget.Data := proj fst
noncomputable def b : Code Pack RawBox.Data := proj (snd ≫ₚ fst)
noncomputable def t : Code Pack Count := proj (snd ≫ₚ snd ≫ₚ fst)
noncomputable def q : Code Pack (List W) := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ fst)
noncomputable def r : Code Pack (List W) := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ fst)
noncomputable def vs : Code Pack (List (List W)) := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ fst)
noncomputable def o : Code Pack Orient := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ fst)
noncomputable def os : Code Pack (List Orient) := proj (snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd ≫ₚ snd)

@[simp] theorem p_eval (z : Pack) : p z=z.p := rfl
@[simp] theorem b_eval (z : Pack) : b z=z.b := rfl
@[simp] theorem t_eval (z : Pack) : t z=z.t := rfl
@[simp] theorem q_eval (z : Pack) : q z=z.q := rfl
@[simp] theorem r_eval (z : Pack) : r z=z.r := rfl
@[simp] theorem vs_eval (z : Pack) : vs z=z.vs := rfl
@[simp] theorem o_eval (z : Pack) : o z=z.o := rfl
@[simp] theorem os_eval (z : Pack) : os z=z.os := rfl

noncomputable def pack {α : Type} [Encoding α]
    (p : Code α RawBudget.Data := const zeroBudget)
    (b : Code α RawBox.Data := const zeroBox)
    (t : Code α Count := const [])
    (q r : Code α (List W) := const [])
    (vs : Code α (List (List W)) := const [])
    (o : Code α Orient := const (false,[]))
    (os : Code α (List Orient) := const []) : Code α Pack :=
  (p ⋏ₚ b ⋏ₚ t ⋏ₚ q ⋏ₚ r ⋏ₚ vs ⋏ₚ o ⋏ₚ os).recode _root_.id
    (fun x => ⟨p x,b x,t x,q x,r x,vs x,o x,os x⟩) (fun _ => rfl) (fun _ => rfl)
@[simp] theorem pack_eval {α : Type} [Encoding α]
    (p : Code α RawBudget.Data) (b : Code α RawBox.Data) (t : Code α Count)
    (q r : Code α (List W)) (vs : Code α (List (List W))) (o : Code α Orient) (os : Code α (List Orient)) (x : α) :
    pack p b t q r vs o os x=⟨p x,b x,t x,q x,r x,vs x,o x,os x⟩ := rfl

abbrev Cell := Count×Pack
abbrev State := Cell×List Cell
abbrev Env := RawBasic.Arena×Count×Count×Count×Count

noncomputable def arena : Code Env RawBasic.Arena := fst
noncomputable def exponent : Code Env Count := snd ≫ₚ fst
noncomputable def samples : Code Env Count := snd ≫ₚ snd ≫ₚ fst
noncomputable def trials : Code Env Count := snd ≫ₚ snd ≫ₚ snd ≫ₚ fst
noncomputable def basicSteps : Code Env Count := snd ≫ₚ snd ≫ₚ snd ≫ₚ snd

abbrev Input := Env×Count×State
noncomputable def env : Code Input Env := fst
noncomputable def random : Code Input Count := snd ≫ₚ fst
noncomputable def state : Code Input State := snd ≫ₚ snd
noncomputable def current : Code Input Pack := state ≫ₚ fst ≫ₚ snd
noncomputable def stack : Code Input (List Cell) := state ≫ₚ snd
noncomputable def caller : Code Input Pack := stack ≫ₚ head ([],Pack.zero) ≫ₚ snd
noncomputable def rest : Code Input (List Cell) := stack ≫ₚ tail
noncomputable def makeCell {α : Type} [Encoding α] (tag : ℕ) (c : Code α Pack) : Code α Cell :=
  const (List.replicate tag ()) ⋏ₚ c
noncomputable def call {α : Type} [Encoding α] (tag : ℕ) (c : Code α Pack) (k : Code α (List Cell)) : Code α State :=
  makeCell tag c ⋏ₚ k
noncomputable def ret {α : Type} [Encoding α] (c : Code α Pack) (k : Code α (List Cell)) : Code α State := call 10 c k
noncomputable def push {α : Type} [Encoding α] (tag : ℕ) (c : Code α Pack) (k : Code α (List Cell)) : Code α (List Cell) :=
  (makeCell tag c ⋏ₚ k) ≫ₚ cons
noncomputable def save (tag : ℕ) : Code Input (List Cell) := push tag current stack
noncomputable def smallWidth (x : Code Input RawBox.Data) : Code Input Bool :=
  ((x ≫ₚ RawBox.width) ⋏ₚ (env ≫ₚ samples ≫ₚ Counter.word ≫ₚ RawBudget.times 128)) ≫ₚ Word.le
noncomputable def basic (x : Code Input RawBox.Data) : Code Input (List W) :=
  (((env ≫ₚ arena) ⋏ₚ x) ⋏ₚ (env ≫ₚ basicSteps)) ≫ₚ RawBasic.solve
noncomputable def narrow (x : Code Input RawBox.Data) (v : Code Input (List W)) : Code Input RawBox.Data :=
  (((x ⋏ₚ (((env ≫ₚ exponent) ⋏ₚ const (List.replicate 5 ())) ≫ₚ Counter.add)) ≫ₚ RawBox.dividedWidth) ⋏ₚ v) ≫ₚ RawBox.centered
noncomputable def wide (x : Code Input RawBox.Data) (v : Code Input (List W)) : Code Input RawBox.Data :=
  (((x ⋏ₚ const (List.replicate 3 ())) ≫ₚ RawBox.dividedWidth) ⋏ₚ v) ≫ₚ RawBox.centered
noncomputable def delta (x : Code Input RawBox.Data) : Code Input W :=
  (x ⋏ₚ (((env ≫ₚ exponent) ⋏ₚ const (List.replicate 2 ())) ≫ₚ Counter.add)) ≫ₚ RawBox.dividedWidth
noncomputable def capWidth (x : Code Input RawBox.Data) : Code Input W :=
  ((x ≫ₚ RawBox.width) ⋏ₚ delta x) ≫ₚ Word.sub

noncomputable def solveCase : Code Input State :=
  Code.branch (current ≫ₚ p ≫ₚ RawBudget.small)
    (ret (pack (q:=((current ≫ₚ p) ⋏ₚ (current ≫ₚ b)) ≫ₚ RawBox.smallVector)) stack)
    (Code.branch (smallWidth (current ≫ₚ b))
      (ret (pack (q:=basic (current ≫ₚ b))) stack)
      (call 8 (pack (current ≫ₚ p) (current ≫ₚ b)) (save 15)))
noncomputable def askCase : Code Input State :=
  call 2 (pack (current ≫ₚ p) (current ≫ₚ b) (env ≫ₚ trials)) (save 2)
noncomputable def trialsCase : Code Input State :=
  Code.branch (current ≫ₚ t ≫ₚ empty)
    (ret (pack (vs:=const [])) stack)
    (call 0 current (push 0 (pack (current ≫ₚ p) (current ≫ₚ b) (current ≫ₚ t ≫ₚ tail)) stack))
noncomputable def updateCase : Code Input State :=
  call 1 (pack (current ≫ₚ p ≫ₚ RawBudget.reduceK) (narrow (current ≫ₚ b) (current ≫ₚ q))) (save 3)
noncomputable def centersCase : Code Input State :=
  Code.branch (current ≫ₚ t ≫ₚ empty)
    (ret (pack (vs:=((current ≫ₚ q) ⋏ₚ const []) ≫ₚ cons)) stack)
    (call 3 current (push 5 (pack (current ≫ₚ p) (current ≫ₚ b) (current ≫ₚ t ≫ₚ tail) (current ≫ₚ q)) stack))
noncomputable def orientCase : Code Input State :=
  Code.branch (smallWidth (current ≫ₚ b))
    (ret (pack (o:=((current ≫ₚ p) ⋏ₚ (current ≫ₚ b) ⋏ₚ basic (current ≫ₚ b)) ≫ₚ RawOrientation.base)) stack)
    (call 4 (pack (current ≫ₚ p) (current ≫ₚ b) (env ≫ₚ samples) (current ≫ₚ b ≫ₚ RawBox.midpoint)) (save 6))
noncomputable def orientTrialsCase : Code Input State :=
  Code.branch (current ≫ₚ t ≫ₚ empty) (ret (pack (os:=const [])) stack)
    (call 5 current (push 8 (pack (current ≫ₚ p) (current ≫ₚ b) (current ≫ₚ t ≫ₚ tail)) stack))
noncomputable def orientPlusCase : Code Input State :=
  call 6 (pack (current ≫ₚ p) (current ≫ₚ b) (env ≫ₚ trials)) (save 10)
noncomputable def tightenCase : Code Input State :=
  call 1 (pack (current ≫ₚ p ≫ₚ RawBudget.reduceK) (current ≫ₚ b)) (save 11)
noncomputable def reweightCase : Code Input State :=
  Code.branch (current ≫ₚ o ≫ₚ snd ≫ₚ empty) (ret (pack (vs:=const [])) stack)
    (call 1 (pack
      (Code.branch (current ≫ₚ o ≫ₚ fst)
        (((current ≫ₚ p) ⋏ₚ (current ≫ₚ o ≫ₚ snd ≫ₚ head [])) ≫ₚ RawBudget.reweightM)
        (((current ≫ₚ p) ⋏ₚ (current ≫ₚ o ≫ₚ snd ≫ₚ head [])) ≫ₚ RawBudget.reweightK))
      (current ≫ₚ b))
      (push 17 (pack (current ≫ₚ p) (current ≫ₚ b)
        (o:=(current ≫ₚ o ≫ₚ fst) ⋏ₚ (current ≫ₚ o ≫ₚ snd ≫ₚ tail))) stack))
end RawControl
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Array

theorem fold_select_bound (f : Code (W×W) W) (hf : ∀ z, f z=z.1 ∨ f z=z.2)
    {N : ℕ} {xs : List W} {xss : List (List W)} (h : Bounded xs N)
    (hs : ∀ ys∈xss, Bounded ys N) :
    Bounded (Fold.fold (zip zero zero f).eval xs xss) N ∧
      (Fold.fold (zip zero zero f).eval xs xss).length=xs.length := by
  induction xss generalizing xs with
  | nil => exact ⟨h,rfl⟩
  | cons ys yss ih =>
    change Bounded (Fold.fold _ (zip zero zero f (xs,ys)) yss) N ∧ _
    have hh := ih (bounded_zip h (hs ys (by simp)) f hf) (fun zs hz => hs zs (by simp [hz]))
    exact ⟨hh.1,hh.2.trans (zip_length f.eval zero xs ys)⟩

noncomputable def foldSelect (f : Code (W×W) W) (hf : ∀ z, f z=z.1 ∨ f z=z.2) :
    Code (List W×List (List W)) (List W) :=
  foldPrefix (zip zero zero f) 20 2 (by
    intro xs xss k _hk
    let S := treeSize (encode (xs,xss))
    have hx : Bounded xs S := fun w hw => (digits_le_wordSize w).trans ((Size.mem hw).trans (Size.fst (xs,xss)))
    have hxs : ∀ ys∈xss.take k, Bounded ys S := by
      intro ys hy w hw
      exact (digits_le_wordSize w).trans ((Size.mem hw).trans
        ((Size.mem (List.mem_of_mem_take hy)).trans (Size.snd (xs,xss))))
    have hb := fold_select_bound f hf hx hxs
    have ht := size_bound hb.1
    rw [hb.2] at ht
    have hl := (Size.length xs).trans (Size.fst (xs,xss))
    change xs.length≤S at hl
    have hm := Nat.mul_le_mul_right (4*S+6) hl
    calc
      treeSize (encode (Fold.fold (zip zero zero f).eval xs (xss.take k))) ≤ xs.length*(4*S+6)+1 := ht
      _ ≤ 20*(S+1)^2 := by nlinarith)
noncomputable def foldMin : Code (List W×List (List W)) (List W) := foldSelect Word.min EdgeScan.low_mem
noncomputable def foldMax : Code (List W×List (List W)) (List W) := foldSelect Word.max EdgeScan.high_mem

theorem foldMin_rep {n B : ℕ} {I : SolveBox n B} (v : BoxVector I) {xs : List W}
    (hv : VectorRep v.val xs) {vs : List (BoxVector I)} {xss : List (List W)}
    (hs : VectorsRep (vs.map Subtype.val) xss) :
    VectorRep (vs.foldl I.minVector v).val (foldMin (xs,xss)) := by
  induction vs generalizing v xs xss with
  | nil => cases hs; exact hv
  | cons w ws ih =>
    cases hs with
    | cons hw hws =>
      exact ih (I.minVector v w) (Array.zip_rep Word.min Min.min (fun _ _ => Word.min_val _ _) hv hw) hws

theorem foldMax_rep {n B : ℕ} {I : SolveBox n B} (v : BoxVector I) {xs : List W}
    (hv : VectorRep v.val xs) {vs : List (BoxVector I)} {xss : List (List W)}
    (hs : VectorsRep (vs.map Subtype.val) xss) :
    VectorRep (vs.foldl I.maxVector v).val (foldMax (xs,xss)) := by
  induction vs generalizing v xs xss with
  | nil => cases hs; exact hv
  | cons w ws ih =>
    cases hs with
    | cons hw hws =>
      exact ih (I.maxVector v w) (Array.zip_rep Word.max Max.max (fun _ _ => Word.max_val _ _) hv hw) hws
end Array
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

noncomputable def trialsHeadCase : Code Input State :=
  call 2 (pack (caller ≫ₚ p) (caller ≫ₚ b) (caller ≫ₚ t))
    (push 1 (pack (q:=current ≫ₚ q)) rest)
noncomputable def vectorConsCase : Code Input State :=
  ret (pack (vs:=((caller ≫ₚ q) ⋏ₚ (current ≫ₚ vs)) ≫ₚ cons)) rest
noncomputable def medianCase : Code Input State :=
  ret (pack (q:=((caller ≫ₚ b) ⋏ₚ (current ≫ₚ vs)) ≫ₚ RawMedian.boxed)) rest
noncomputable def centerFirstCase : Code Input State :=
  call 1 (pack (caller ≫ₚ p ≫ₚ RawBudget.reduceM) (narrow (caller ≫ₚ b) (caller ≫ₚ q)))
    (push 4 (pack (b:=caller ≫ₚ b) (r:=current ≫ₚ q)) rest)
noncomputable def centerSecondCase : Code Input State :=
  ret (pack (q:=((caller ≫ₚ b) ⋏ₚ (caller ≫ₚ r) ⋏ₚ (current ≫ₚ q)) ≫ₚ RawBox.averageClipped)) rest
noncomputable def centersHeadCase : Code Input State :=
  call 4 (pack (caller ≫ₚ p) (caller ≫ₚ b) (caller ≫ₚ t) (current ≫ₚ q))
    (push 1 (pack (q:=caller ≫ₚ q)) rest)
noncomputable def centerAt (index : Code Input Count) : Code Input (List W) :=
  (((current ≫ₚ vs) ⋏ₚ index) ⋏ₚ (caller ≫ₚ b ≫ₚ RawBox.midpoint)) ≫ₚ getD []
noncomputable def lastPositive : Code Input (List Bool) :=
  ((caller ≫ₚ b) ⋏ₚ (env ≫ₚ samples ≫ₚ Counter.word) ⋏ₚ centerAt (env ≫ₚ samples)) ≫ₚ RawOrientation.positives
noncomputable def lastNegative : Code Input (List Bool) :=
  ((caller ≫ₚ b) ⋏ₚ (env ≫ₚ samples ≫ₚ Counter.word) ⋏ₚ centerAt (env ≫ₚ samples)) ≫ₚ RawOrientation.negatives
noncomputable def orientLoopCase : Code Input State :=
  Code.branch (((caller ≫ₚ p) ⋏ₚ lastPositive) ≫ₚ RawBudget.measureLarge)
    (ret (pack (o:=lastPositive ≫ₚ RawOrientation.trueComplement)) rest)
    (Code.branch (((caller ≫ₚ p) ⋏ₚ lastNegative) ≫ₚ RawBudget.measureLarge)
      (ret (pack (o:=lastNegative ≫ₚ RawOrientation.falseComplement)) rest)
      (call 5 (pack (caller ≫ₚ p) (wide (caller ≫ₚ b) (centerAt random)))
        (push 7 (pack (o:=const false ⋏ₚ ((lastPositive ⋏ₚ ((lastNegative ⋏ₚ const []) ≫ₚ cons)) ≫ₚ cons))) rest)))
noncomputable def orientTailCase : Code Input State :=
  ret (pack (o:=((current ≫ₚ o) ⋏ₚ (caller ≫ₚ o ≫ₚ snd ≫ₚ head []) ⋏ₚ
    (caller ≫ₚ o ≫ₚ snd ≫ₚ tail ≫ₚ head [])) ≫ₚ RawOrientation.extend)) rest
noncomputable def orientHeadCase : Code Input State :=
  call 6 (pack (caller ≫ₚ p) (caller ≫ₚ b) (caller ≫ₚ t))
    (push 9 (pack (o:=current ≫ₚ o)) rest)
noncomputable def orientConsCase : Code Input State :=
  ret (pack (os:=((caller ≫ₚ o) ⋏ₚ (current ≫ₚ os)) ≫ₚ cons)) rest
noncomputable def combineCase : Code Input State :=
  ret (pack (o:=current ≫ₚ os ≫ₚ RawOrientation.combine)) rest
noncomputable def tightenFirstCase : Code Input State :=
  Code.branch (((caller ≫ₚ b) ⋏ₚ (current ≫ₚ q) ⋏ₚ delta (caller ≫ₚ b)) ≫ₚ RawBox.movedFloor)
    (call 8 (pack (caller ≫ₚ p) (((caller ≫ₚ b) ⋏ₚ (current ≫ₚ q)) ≫ₚ RawBox.withFloor))
      (push 13 (pack (b:=caller ≫ₚ b) (q:=current ≫ₚ q)) rest))
    (call 1 (pack (caller ≫ₚ p ≫ₚ RawBudget.reduceM) (caller ≫ₚ b)) (push 12 caller rest))
noncomputable def tightenSecondCase : Code Input State :=
  Code.branch (((caller ≫ₚ b) ⋏ₚ (current ≫ₚ q) ⋏ₚ delta (caller ≫ₚ b)) ≫ₚ RawBox.movedCeiling)
    (call 8 (pack (caller ≫ₚ p) (((caller ≫ₚ b) ⋏ₚ (current ≫ₚ q)) ≫ₚ RawBox.withCeiling))
      (push 14 (pack (b:=caller ≫ₚ b) (q:=current ≫ₚ q)) rest))
    (ret (pack (b:=caller ≫ₚ b)) rest)
noncomputable def boxPassCase : Code Input State := ret (pack (b:=current ≫ₚ b)) rest
noncomputable def solveTightCase : Code Input State :=
  call 7 (pack (caller ≫ₚ p) (current ≫ₚ b))
    (push 16 (pack (caller ≫ₚ p) (current ≫ₚ b)) (push 21 (const Pack.zero) rest))
noncomputable def solveOrientedCase : Code Input State :=
  call 9 (pack (caller ≫ₚ p) (caller ≫ₚ b) (o:=current ≫ₚ o))
    (push 18 (pack (caller ≫ₚ p) (caller ≫ₚ b) (o:=(current ≫ₚ o ≫ₚ fst) ⋏ₚ const [])) rest)
noncomputable def reweightHeadCase : Code Input State :=
  call 9 (pack (caller ≫ₚ p) (caller ≫ₚ b) (o:=caller ≫ₚ o))
    (push 1 (pack (q:=current ≫ₚ q)) rest)
noncomputable def solveReweightedCase : Code Input State :=
  Code.branch (caller ≫ₚ o ≫ₚ fst)
    (call 0 (pack (caller ≫ₚ p) (((caller ≫ₚ b) ⋏ₚ capWidth (caller ≫ₚ b)) ≫ₚ RawBox.capHigh))
      (push 19 (pack (b:=caller ≫ₚ b) (vs:=current ≫ₚ vs)) rest))
    (call 0 (pack (caller ≫ₚ p) (((caller ≫ₚ b) ⋏ₚ capWidth (caller ≫ₚ b)) ≫ₚ RawBox.capLow))
      (push 20 (pack (b:=caller ≫ₚ b) (vs:=current ≫ₚ vs)) rest))
noncomputable def capHighCase : Code Input State :=
  ret (pack (q:=((current ≫ₚ q) ⋏ₚ (caller ≫ₚ vs)) ≫ₚ Array.foldMin)) rest
noncomputable def capLowCase : Code Input State :=
  ret (pack (q:=((current ≫ₚ q) ⋏ₚ (caller ≫ₚ vs)) ≫ₚ Array.foldMax)) rest
noncomputable def includeInnerCase : Code Input State := ret (pack (q:=current ≫ₚ q)) rest

noncomputable def resume : Code Input State :=
  Code.branch (stack ≫ₚ empty) state
    (select (stack ≫ₚ head ([],Pack.zero) ≫ₚ fst)
      [trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,centersHeadCase,
       orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,tightenFirstCase,
       tightenSecondCase,boxPassCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,
       solveReweightedCase,capHighCase,capLowCase,includeInnerCase] state)

noncomputable def dispatch : Code Input State :=
  select (state ≫ₚ fst ≫ₚ fst)
    [solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,orientPlusCase,
      tightenCase,reweightCase] resume
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.SourceControl

def sampledResume {G : Game} {B : ℕ} {A C R : Result G B} (f : Frame G B A C) (v : A.Value)
    (k : Kont G B C R) (j : ℕ) : State G B R :=
  match f with
  | .trialsHead P I J => (.call (.trials P I J) (.push (.vectorCons v) k))
  | .vectorCons a => (.ret k (a :: v))
  | .median I => (.ret k (I.medianBox v))
  | .centerFirst P _ I hB q =>
      (.call (.ask P.reduceM (I.narrowCentered hB q.val)) (.push (.centerSecond I hB q v) k))
  | .centerSecond I _ _ r => (.ret k (I.averageClipped r.val v.val))
  | .centersHead P hR I hB t q =>
      (.call (.centers P hR I hB t v) (.push (.vectorCons q) k))
  | .orientLoop P hR I hB =>
      let H := PositiveDisplacement I (v.getD (globalS B) I.midpoint)
      let N := NegativeDisplacement I (v.getD (globalS B) I.midpoint)
      if hH : 1 / 2 < P.measure H then
        (.ret k ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩)
      else if hN : 1 / 2 < P.measure N then
        (.ret k ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩)
      else
        .call (.orient P hR (I.wideCentered hB (v.getD j I.midpoint).val))
            (.push (.orientTail ⟨H, le_of_not_gt hH⟩ ⟨N, le_of_not_gt hN⟩) k)
  | .orientTail H N => (.ret k ⟨v.chooseY, v.exceptions ++ [H, N]⟩)
  | .orientHead P hR I J => (.call (.orientTrials P hR I J) (.push (.orientCons v) k))
  | .orientCons O => (.ret k (O :: v))
  | .combine _ => (.ret k (combineOrientations v))
  | .tightenFirst P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ v.val i - I.a i then
        (.call (.tighten P hR (I.withFloor v) hB) (.push (.floor I v) k))
      else (.call (.ask P.reduceM I) (.push (.tightenSecond P hR I hB) k))
  | .tightenSecond P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ I.b i - v.val i then
        (.call (.tighten P hR (I.withCeiling v) hB) (.push (.ceiling I v) k))
      else (.ret k ⟨I, rfl, le_refl _, le_refl _⟩)
  | .floor _ q => (.ret k ⟨v.box, v.width_eq, q.property.1.trans v.floor_le, v.ceiling_le⟩)
  | .ceiling _ q => (.ret k ⟨v.box, v.width_eq, v.floor_le, v.ceiling_le.trans q.property.2⟩)
  | .solveTight P hR _ hB =>
      have hK : 128 * globalS B < v.box.width := by rw [v.width_eq]; exact hB
      (.call (.orientPlus P hR v.box) (.push (.solveOriented P hR v.box hK) (.push (.includeInner v) k)))
  | .solveOriented P hR I hB =>
      (.call (.reweight P hR I v.chooseY v.exceptions) (.push (.solveReweighted P hR I hB v.chooseY) k))
  | .reweightHead P hR I side Hs => (.call (.reweight P hR I side Hs) (.push (.vectorCons v) k))
  | .solveReweighted P _ I hB side =>
      if side then (.call (.solve P (I.capHigh I.C I.C_positive (I.C_smaller hB).le)) (.push (.capHigh I hB v) k))
      else (.call (.solve P (I.capLow I.C I.C_positive (I.C_smaller hB).le)) (.push (.capLow I hB v) k))
  | .capHigh I hB rs => (.ret k (rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le v)))
  | .capLow I hB rs => (.ret k (rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le v)))
  | .includeInner T => (.ret k (T.include v))

def sampledStep {G : Game} {B : ℕ} {R : Result G B} (j : ℕ) : State G B R → State G B R
  | .ret .done v => (.ret .done v)
  | .ret (.push f k) v => sampledResume f v k j
  | .call job k => match job with
    | .solve P I => if hR : P.parameter < 1 then (.ret k (I.smallVector P))
        else if hB : I.width ≤ 128 * globalS B then (.ret k (I.exactVector G))
        else (.call (.tighten P (le_of_not_gt hR) I (by omega)) (.push (.solveTight P (le_of_not_gt hR) I (by omega)) k))
    | .ask P I => (.call (.trials P I (globalJ G.n B)) (.push (.median I) k))
    | .trials P I J => match J with
      | 0 => (.ret k [])
      | J + 1 => (.call (.solve P I) (.push (.trialsHead P I J) k))
    | .update P hR I hB q =>
        (.call (.ask P.reduceK (I.narrowCentered hB q.val)) (.push (.centerFirst P hR I hB q) k))
    | .centers P hR I hB t q => match t with
      | 0 => (.ret k [q])
      | t + 1 => (.call (.update P hR I hB q) (.push (.centersHead P hR I hB t q) k))
    | .orient P hR I =>
        if hB : I.width ≤ 128 * globalS B then (.ret k (orientBase G P I))
        else (.call (.centers P hR I (by omega) (globalS B) I.midpoint) (.push (.orientLoop P hR I (by omega)) k))
    | .orientTrials P hR I J => match J with
      | 0 => (.ret k [])
      | J + 1 => (.call (.orient P hR I) (.push (.orientHead P hR I J) k))
    | .orientPlus P hR I => (.call (.orientTrials P hR I (globalJ G.n B)) (.push (.combine P) k))
    | .tighten P hR I hB => (.call (.ask P.reduceK I) (.push (.tightenFirst P hR I hB) k))
    | .reweight P hR I side Hs => match Hs with
      | [] => (.ret k [])
      | H :: Hs =>
          (.call (.ask (if side then P.reweightM H.val else P.reweightK H.val) I)
            (.push (.reweightHead P hR I side Hs) k))

end MeanPayoff.SourceControl

end

end OAI
