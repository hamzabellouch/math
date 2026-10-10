import OAI.Computability.MeanPayoff.Main

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Code
variable {α β ρ : Type} [Encoding α] [Encoding β] [Encoding ρ]
noncomputable def stream (f : Code (α×ρ) (β×ρ))
    (hr : ∀ p r, treeSize (encode (f (p,r)).2)≤treeSize (encode r)) :
    Code ((α×List β×ρ)×Count) (α×List β×ρ) :=
  ⟨fun z => Fold.fold (StreamFold.step f.eval) z.1 z.2,
    Fold.device (StreamFold.stepDevice f.device),StreamFold.polynomial f.device f.polynomial hr⟩
end Code

namespace Counter
noncomputable def enumRow : Code (Unit×Count) (Count×Count) := (snd ≫ₚ tail) ⋏ₚ (snd ≫ₚ tail)
noncomputable def enumLoop : Code ((Unit×List Count×Count)×Count) (Unit×List Count×Count) :=
  stream enumRow (by
    intro u r
    cases r with
    | nil => exact le_rfl
    | cons a r =>
      change treeSize (listTree Median.unitData r)≤treeSize (listTree Median.unitData (a::r))
      rw [listTree,treeSize_pair]
      omega)
noncomputable def enum : Code Count (List Count) :=
  (((const () ⋏ₚ const [] ⋏ₚ Code.id) ⋏ₚ Code.id) ≫ₚ enumLoop) ≫ₚ snd ≫ₚ fst

theorem canonical (c : Count) : c=List.replicate c.length () :=
  List.eq_replicate_of_mem (fun _ _ => Subsingleton.elim _ _)

theorem enumLoop_eq (c : Count) (acc : List Count) :
    enumLoop (((),acc,c),c)=((),(List.range c.length).map (fun i => List.replicate i ())++acc,[]) := by
  change Fold.fold (StreamFold.step enumRow.eval) ((),acc,c) c=_
  induction c generalizing acc with
  | nil => rfl
  | cons u cs ih =>
    change Fold.fold (StreamFold.step enumRow.eval) ((),cs::acc,cs) cs=_
    rw [ih]
    simp only [List.length_cons,List.range_succ,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
      List.cons_append,List.nil_append]
    rw [←canonical cs]

theorem enum_eq (c : Count) : enum c=(List.range c.length).map (fun i => List.replicate i ()) := by
  change (enumLoop (((),[],c),c)).2.1=_
  rw [enumLoop_eq,List.append_nil]

theorem enum_ofFn (c : Count) : enum c=List.ofFn (fun i : Fin c.length => List.replicate i.val ()) := by
  rw [enum_eq,List.ofFn_eq_map]
  rw [←List.map_coe_finRange_eq_range]
  rw [List.map_map]
  rfl
end Counter

def VectorsRep {n : ℕ} (vs : List (Fin n→ℤ)) (xss : List (List W)) : Prop :=
  List.Forall₂ VectorRep vs xss

theorem VectorRep.length {n : ℕ} {v : Fin n→ℤ} {xs : List W} (h : VectorRep v xs) : xs.length=n := by
  obtain ⟨ws,rfl,_⟩ := h
  exact List.length_ofFn

theorem VectorRep.nth {n : ℕ} {v : Fin n→ℤ} {xs : List W} (h : VectorRep v xs) (i : Fin n) :
    (Code.nth Array.zero (xs,List.replicate i.val ())).val=v i := by
  obtain ⟨ws,rfl,hws⟩ := h
  change (Graph.lookup (Graph.codePot ws,List.replicate i.val ())).val=_
  rw [Graph.lookup_exact,hws]

namespace RawMedian
noncomputable def scalar : Code (List W) W := ⟨Median.median,Median.device,Median.polynomial⟩
noncomputable def entry : Code (Count×List W) W := swap ≫ₚ nth Array.zero
noncomputable def column : Code (List (List W)×Count) W := swap ≫ₚ envMap entry ≫ₚ scalar
noncomputable def coordinates : Code (Count×List (List W)) (List W) :=
  (snd ⋏ₚ (fst ≫ₚ Counter.enum)) ≫ₚ envMap column
noncomputable def boxed : Code (RawBox.Data×List (List W)) (List W) :=
  Code.branch (snd ≫ₚ empty) (fst ≫ₚ RawBox.lower)
    (((fst ≫ₚ RawBox.lower ≫ₚ count) ⋏ₚ snd) ≫ₚ coordinates)

theorem column_values {n : ℕ} {vs : List (Fin n→ℤ)} {xss : List (List W)}
    (h : VectorsRep vs xss) (i : Fin n) :
    (xss.map (fun xs => entry (List.replicate i.val (),xs))).map SignedBits.Word.val=
      vs.map (fun v => v i) := by
  induction h with
  | nil => rfl
  | cons h hrest ih =>
    simp only [List.map_cons]
    rw [show (entry (List.replicate i.val (),_)).val=_ from h.nth i,ih]

theorem coordinates_rep {n : ℕ} {vs : List (Fin n→ℤ)} {xss : List (List W)}
    (h : VectorsRep vs xss) (c : Count) (hc : c.length=n) :
    VectorRep (MeanPayoff.median vs) (coordinates (c,xss)) := by
  subst n
  refine ⟨fun i => column (xss,List.replicate i.val ()),?_,?_⟩
  · change List.map _ (Counter.enum c)=_
    rw [Counter.enum_ofFn,List.map_ofFn]
    rfl
  · intro i
    change (Median.median (xss.map (fun xs => entry (List.replicate i.val (),xs)))).val=_
    rw [Median.value_exact,column_values h i]
    rfl

theorem boxed_rep {n B : ℕ} {I : SolveBox n B} {b : RawBox.Data} (hb : RawBox.Rep I b)
    (vs : List (BoxVector I)) {xss : List (List W)}
    (h : VectorsRep (vs.map Subtype.val) xss) :
    VectorRep (I.medianBox vs).val (boxed (b,xss)) := by
  have hl := h.length_eq
  simp only [List.length_map] at hl
  by_cases he : xss=[]
  · have hv : vs=[] := List.length_eq_zero_iff.mp (by rw [hl,he]; rfl)
    subst xss
    subst vs
    simpa [boxed,SolveBox.medianBox,SolveBox.bottom,RawBox.lower] using hb.lower
  · have hp : 0<vs.length := by have := List.length_pos_iff.mpr he; omega
    simp only [boxed,Code.branch_eval,Code.comp_eval,Code.snd_eval,Code.fst_eval,Code.empty_eval]
    rw [show xss.isEmpty=false by cases xss <;> simp_all]
    simp only [Bool.false_eq_true,ite_false,SolveBox.medianBox,dite_eq_left hp,Code.pair_eval]
    apply coordinates_rep h
    simpa only [Code.comp_eval,Code.fst_eval,Code.count,Code.map_eval,List.length_map,RawBox.lower,
      Code.snd_eval] using hb.lower.length

end RawMedian
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Code
variable {α : Type} [Encoding α]
noncomputable def getD (a : α) : Code ((List α×Count)×α) α :=
  Code.branch (fst ≫ₚ drop ≫ₚ empty) snd (fst ≫ₚ drop ≫ₚ head a)
@[simp] theorem getD_eval (a : α) (z : (List α×Count)×α) :
    getD a z=z.1.1.getD z.1.2.length z.2 := by
  simp only [getD,branch_eval,comp_eval,fst_eval,snd_eval,empty_eval,head_eval]
  change (if (z.1.1.drop z.1.2.length).isEmpty then z.2 else
    (z.1.1.drop z.1.2.length).headD a)=_
  rw [List.getD_eq_getElem?_getD,←List.head?_drop]
  generalize z.1.1.drop z.1.2.length=xs
  cases xs <;> rfl
end Code

namespace Array
noncomputable def scalarLT : Code (W×List W) (List Bool) := envMap Word.lt
noncomputable def scalarLE : Code (W×List W) (List Bool) := envMap Word.le
noncomputable def belowScalar : Code (W×List W) (List Bool) := envMap (swap ≫ₚ Word.lt)

theorem scalarTest_rep {n : ℕ} {v : Fin n→ℤ} {xs : List W} (h : VectorRep v xs)
    (w : W) (f : Code (W×W) Bool) (p : ℤ→ℤ→Prop) [DecidableRel p]
    (hf : ∀ a b, f (a,b)=decide (p a.val b.val)) :
    MaskRep (Finset.univ.filter (fun i => p w.val (v i))) (envMap f (w,xs)) := by
  obtain ⟨ws,rfl,hws⟩ := h
  unfold MaskRep
  simp only [Code.envMap_eval,List.map_ofFn]
  congr 1
  funext i
  simp [hf,hws]

end Array

namespace RawOrientation
abbrev Data := Bool×List (List Bool)
def Rep {n : ℕ} {P : Budgets n} (O : Orientation P) (o : Data) : Prop :=
  o.1=O.chooseY ∧ List.Forall₂ (fun H hs => MaskRep H.val hs) O.exceptions o.2
def ManyRep {n : ℕ} {P : Budgets n} (os : List (Orientation P)) (rs : List Data) : Prop :=
  List.Forall₂ Rep os rs

noncomputable def positives : Code (RawBox.Data×W×List W) (List Bool) :=
  ((fst ≫ₚ RawBox.width ≫ₚ Word.double) ⋏ₚ
    (((snd ≫ₚ fst) ⋏ₚ (((snd ≫ₚ snd) ⋏ₚ (fst ≫ₚ RawBox.midpoint)) ≫ₚ Array.sub)) ≫ₚ Array.scale)) ≫ₚ Array.scalarLT
noncomputable def negatives : Code (RawBox.Data×W×List W) (List Bool) :=
  ((fst ≫ₚ RawBox.width ≫ₚ Word.double ≫ₚ Word.neg) ⋏ₚ
    (((snd ≫ₚ fst) ⋏ₚ (((snd ≫ₚ snd) ⋏ₚ (fst ≫ₚ RawBox.midpoint)) ≫ₚ Array.sub)) ≫ₚ Array.scale)) ≫ₚ Array.belowScalar
noncomputable def baseMask : Code (RawBox.Data×List W) (List Bool) :=
  ((fst ≫ₚ RawBox.width) ⋏ₚ (((snd ⋏ₚ (fst ≫ₚ RawBox.lower)) ≫ₚ Array.sub) ≫ₚ map Word.double)) ≫ₚ Array.scalarLE
noncomputable def singleton : Code (Bool×List Bool) Data := fst ⋏ₚ ((snd ⋏ₚ const []) ≫ₚ cons)
noncomputable def trueComplement : Code (List Bool) Data :=
  (const true ⋏ₚ Array.complement) ≫ₚ singleton
noncomputable def falseComplement : Code (List Bool) Data :=
  (const false ⋏ₚ Array.complement) ≫ₚ singleton
noncomputable def baseOnMask : Code (RawBudget.Data×List Bool) Data :=
  Code.branch RawBudget.measureLarge (snd ≫ₚ trueComplement) ((const false ⋏ₚ snd) ≫ₚ singleton)
noncomputable def base : Code (RawBudget.Data×RawBox.Data×List W) Data :=
  (fst ⋏ₚ (snd ≫ₚ baseMask)) ≫ₚ baseOnMask
noncomputable def extend : Code (Data×List Bool×List Bool) Data :=
  (fst ≫ₚ fst) ⋏ₚ (((fst ≫ₚ snd) ⋏ₚ (((snd ≫ₚ fst) ⋏ₚ (((snd ≫ₚ snd) ⋏ₚ const []) ≫ₚ cons)) ≫ₚ cons)) ≫ₚ append)
noncomputable def combine : Code (List Data) Data :=
  (((count ≫ₚ Counter.word) ⋏ₚ (filter fst ≫ₚ count ≫ₚ Counter.word ≫ₚ Word.double)) ≫ₚ Word.lt) ⋏ₚ
    (map snd ≫ₚ flatten)

theorem positives_rep {n B : ℕ} {I : SolveBox n B} {b : RawBox.Data} (hb : RawBox.Rep I b)
    (q : BoxVector I) {qs : List W} (hq : VectorRep q.val qs) (s : W) (hs : s.val=globalS B) :
    MaskRep (PositiveDisplacement I q) (positives (b,s,qs)) := by
  have hd := Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) hq (RawBox.midpoint_rep hb)
  have hv := Array.scale_rep hd s
  have h := Array.scalarTest_rep hv (Word.double b.1) Word.lt (·<·) Word.lt_eval
  convert h using 1 <;> try rfl
  simp only [PositiveDisplacement,Word.double_val,hb.width,hs]

theorem negatives_rep {n B : ℕ} {I : SolveBox n B} {b : RawBox.Data} (hb : RawBox.Rep I b)
    (q : BoxVector I) {qs : List W} (hq : VectorRep q.val qs) (s : W) (hs : s.val=globalS B) :
    MaskRep (NegativeDisplacement I q) (negatives (b,s,qs)) := by
  have hd := Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) hq (RawBox.midpoint_rep hb)
  have hv := Array.scale_rep hd s
  have h := Array.scalarTest_rep hv (Word.neg (Word.double b.1)) (swap ≫ₚ Word.lt)
    (fun a b => b<a) (by intro a b; exact Word.lt_eval b a)
  convert h using 1 <;> try rfl
  simp only [NegativeDisplacement,Word.neg_val,Word.double_val,hb.width,hs]
  congr 1

theorem baseMask_rep {n B : ℕ} {I : SolveBox n B} {b : RawBox.Data} (hb : RawBox.Rep I b)
    (q : BoxVector I) {qs : List W} (hq : VectorRep q.val qs) :
    MaskRep (Finset.univ.filter (fun i => (I.width:ℤ)≤2*(q.val i-I.a i))) (baseMask (b,qs)) := by
  have hd := Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) hq hb.lower
  have hd' : VectorRep (fun i => 2*(q.val i-I.a i)) (map Word.double (Array.sub (qs,b.2.1))) := by
    obtain ⟨ws,he,hw⟩ := hd
    refine ⟨fun i => Word.double (ws i),?_,?_⟩
    · change List.map _ (Array.sub (qs,b.2.1))=_
      change Array.sub (qs,b.2.1)=_ at he
      rw [he,List.map_ofFn]
      rfl
    · intro i
      rw [Word.double_val,hw]
  convert Array.scalarTest_rep hd' b.1 Word.le (·≤·) Word.le_eval using 1 <;> try rfl
  rw [hb.width]

theorem base_rep (G : Game) {B : ℕ} {I : SolveBox G.n B} {b : RawBox.Data}
    (hb : RawBox.Rep I b) {P : Budgets G.n} {p : RawBudget.Data} (hp : RawBudget.Rep P p)
    {qs : List W} (hq : VectorRep (I.exactVector G).val qs) :
    Rep (orientBase G P I) (base (p,b,qs)) := by
  let H : Finset (Fin G.n) := Finset.univ.filter (fun i => (I.width:ℤ)≤2*((I.exactVector G).val i-I.a i))
  have hm : MaskRep H (baseMask (b,qs)) := baseMask_rep hb _ hq
  have ht := RawBudget.measureLarge_eq G.positive hp hm
  by_cases hh : (1/2:ℚ)<P.measure H
  · have hsrc : orientBase G P I=⟨true,[⟨Hᶜ,by rw [P.measure_compl G.positive]; linarith⟩]⟩ := by
      simp only [orientBase]
      dsimp only [H] at hh ⊢
      rw [dite_eq_left hh]
    rw [hsrc]
    change Rep _ (if RawBudget.measureLarge (p,baseMask (b,qs)) then _ else _)
    simp only [ht,decide_eq_true hh,ite_true]
    exact ⟨rfl,List.Forall₂.cons (Array.complement_rep hm) List.Forall₂.nil⟩
  · have hsrc : orientBase G P I=⟨false,[⟨H,le_of_not_gt hh⟩]⟩ := by
      simp only [orientBase]
      dsimp only [H] at hh ⊢
      rw [dite_eq_right hh]
    rw [hsrc]
    change Rep _ (if RawBudget.measureLarge (p,baseMask (b,qs)) then _ else _)
    rw [ht,ite_eq_right (by simpa using hh)]
    exact ⟨rfl,List.Forall₂.cons hm List.Forall₂.nil⟩

theorem extend_rep {n : ℕ} {P : Budgets n} {O : Orientation P} {o : Data} (ho : Rep O o)
    (H N : SmallSet P) {hs ns : List Bool} (hH : MaskRep H.val hs) (hN : MaskRep N.val ns) :
    Rep ⟨O.chooseY,O.exceptions++[H,N]⟩ (extend (o,hs,ns)) := by
  refine ⟨ho.1,?_⟩
  change List.Forall₂ _ _ (Code.append (o.2,[hs,ns]))
  rw [Code.append_eval]
  exact List.rel_append ho.2 (List.Forall₂.cons hH (List.Forall₂.cons hN List.Forall₂.nil))

theorem choices_length {n : ℕ} {P : Budgets n} {os : List (Orientation P)} {rs : List Data}
    (h : ManyRep os rs) : (rs.filter Prod.fst).length=(os.filter Orientation.chooseY).length := by
  induction h with
  | nil => rfl
  | cons h hr ih =>
    simp only [List.filter_cons]
    rw [h.1]
    split <;> simp_all only [List.length_cons]

theorem exceptions_rep {n : ℕ} {P : Budgets n} {os : List (Orientation P)} {rs : List Data}
    (h : ManyRep os rs) :
    List.Forall₂ (fun H hs => MaskRep H.val hs) (os.map Orientation.exceptions).flatten (rs.map Prod.snd).flatten := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h hr ih =>
    simp only [List.map_cons,List.flatten_cons]
    exact List.rel_append h.2 ih

theorem combine_rep {n : ℕ} {P : Budgets n} {os : List (Orientation P)} {rs : List Data}
    (h : ManyRep os rs) : Rep (combineOrientations os) (combine rs) := by
  refine ⟨?_,?_⟩
  swap
  · simpa only [combine,Code.pair_eval,Code.comp_eval,Code.map_eval,Code.flatten_eval,combineOrientations,Code.snd]
      using exceptions_rep h
  change Word.lt (Counter.word (count rs),Word.double (Counter.word (count (filter fst rs))))=_
  simp only [Word.lt_eval,Counter.word_val,Word.double_val,Code.count_eval,List.length_map,
    Code.filter_eval]
  change decide ((rs.length:ℤ)<2*((rs.filter Prod.fst).length:ℤ))=_
  rw [choices_length h,←h.length_eq]
  change decide ((os.length:ℤ)<2*((os.filter Orientation.chooseY).length:ℤ))=decide _
  congr 1
  norm_cast

end RawOrientation
end MeanPayoff.TreeDevice.Certified

end

end OAI
