import OAI.Computability.MeanPayoff.EncodedArithmetic

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Array
noncomputable def choose : Code (List Bool × List W × List W) (List W) :=
  (fst ⋏ₚ ((snd ≫ₚ fst ⋏ₚ snd ≫ₚ snd) ≫ₚ zip zero zero (fst ⋏ₚ snd))) ≫ₚ
    zip false (zero,zero) (Code.branch fst (snd ≫ₚ fst) (snd ≫ₚ snd))
noncomputable def replicate : Code (W × Count) (List W) := envMap fst
noncomputable def anyLE : Code (W × List W) Bool := envMap Word.le ≫ₚ any Code.id
noncomputable def anyGE : Code (W × List W) Bool := envMap ((snd ⋏ₚ fst) ≫ₚ Word.le) ≫ₚ any Code.id

theorem map_rep {n : ℕ} (f : Code W W) (g : ℤ → ℤ)
    (hf : ∀ w, (f w).val=g w.val) {v : Fin n → ℤ} {xs : List W} (h : VectorRep v xs) :
    VectorRep (fun i => g (v i)) (map f xs) := by
  obtain ⟨ws,rfl,hw⟩ := h
  refine ⟨f.eval ∘ ws,by simp,?_⟩
  intro i
  simp only [Function.comp_apply,hf,hw]

theorem scale_rep {n : ℕ} {v : Fin n → ℤ} {xs : List W} (h : VectorRep v xs) (w : W) :
    VectorRep (fun i => w.val*v i) (scale (w,xs)) := by
  obtain ⟨ws,rfl,hw⟩ := h
  refine ⟨fun i => Word.mul (w,ws i),by simp [scale,Function.comp_def],?_⟩
  intro i
  simp [hw]

theorem translate_rep {n : ℕ} {v : Fin n → ℤ} {xs : List W} (h : VectorRep v xs) (w : W) :
    VectorRep (fun i => w.val+v i) (translate (w,xs)) := by
  obtain ⟨ws,rfl,hw⟩ := h
  refine ⟨fun i => Word.add (w,ws i),by simp [translate,Function.comp_def],?_⟩
  intro i
  simp [hw]

theorem choose_rep {n : ℕ} {H : Finset (Fin n)} {hs : List Bool}
    {a b : Fin n → ℤ} {as bs : List W} (hH : MaskRep H hs) (ha : VectorRep a as) (hb : VectorRep b bs) :
    VectorRep (fun i => if i∈H then a i else b i) (choose (hs,as,bs)) := by
  obtain ⟨ws,rfl,hw⟩ := ha
  obtain ⟨vs,rfl,hv⟩ := hb
  rw [hH]
  refine ⟨fun i => if i∈H then ws i else vs i,?_,?_⟩
  · change Zip.zip _ _ (List.ofFn _) (Zip.zip _ _ (List.ofFn ws) (List.ofFn vs))=_
    rw [zip_ofFn,zip_ofFn]
    congr 1
    funext i
    simp [comp,fst,snd]
  · intro i
    dsimp only
    split_ifs <;> simp_all

theorem lt_rep {n : ℕ} {a b : Fin n → ℤ} {as bs : List W}
    (ha : VectorRep a as) (hb : VectorRep b bs) :
    MaskRep (Finset.univ.filter (fun i => a i<b i)) (lt (as,bs)) := by
  obtain ⟨ws,rfl,hw⟩ := ha
  obtain ⟨vs,rfl,hv⟩ := hb
  change Zip.zip _ _ (List.ofFn ws) (List.ofFn vs)=_
  rw [zip_ofFn]
  simp [Word.lt_eval,hw,hv]
theorem le_rep {n : ℕ} {a b : Fin n → ℤ} {as bs : List W}
    (ha : VectorRep a as) (hb : VectorRep b bs) :
    MaskRep (Finset.univ.filter (fun i => a i≤b i)) (le (as,bs)) := by
  obtain ⟨ws,rfl,hw⟩ := ha
  obtain ⟨vs,rfl,hv⟩ := hb
  change Zip.zip _ _ (List.ofFn ws) (List.ofFn vs)=_
  rw [zip_ofFn]
  simp [Word.le_eval,hw,hv]

theorem complement_rep {n : ℕ} {H : Finset (Fin n)} {hs : List Bool} (h : MaskRep H hs) :
    MaskRep Hᶜ (complement hs) := by
  rw [h]
  simp [MaskRep,complement,Code.not,List.map_ofFn,Function.comp_def]

theorem repeat_rep {n : ℕ} (w : W) (xs : Count) (h : xs.length=n) :
    VectorRep (fun _ : Fin n => w.val) (replicate (w,xs)) := by
  refine ⟨fun _ => w,?_,fun _ => rfl⟩
  simp [replicate,h,List.ofFn_const]

theorem anyLE_eq {n : ℕ} (w : W) {v : Fin n → ℤ} {xs : List W} (h : VectorRep v xs) :
    anyLE (w,xs)=decide (∃ i, w.val≤v i) := by
  obtain ⟨ws,rfl,hw⟩ := h
  simp [anyLE,Code.any,Code.filter,Code.empty,Word.le_eval,hw,← decide_not]

theorem anyGE_eq {n : ℕ} (w : W) {v : Fin n → ℤ} {xs : List W} (h : VectorRep v xs) :
    anyGE (w,xs)=decide (∃ i, v i≤w.val) := by
  obtain ⟨ws,rfl,hw⟩ := h
  simp [anyGE,Code.any,Code.filter,Code.empty,Word.le_eval,hw,← decide_not]
end Array

namespace RawBudget
theorem smallMask_eq {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    MaskRep (Finset.univ.filter (fun i => P.m < P.beta i)) (smallMask p) := by
  obtain ⟨a,b,ha,hb,hap,hbp,hea,heb⟩ := h.coords
  change Zip.zip _ _ (List.map _ p.2.2.2) (List.map _ p.2.2.2)=_
  rw [hb,List.map_ofFn,List.map_ofFn,Array.zip_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,Word.mul_val,Word.lt_eval,Finset.mem_filter,Finset.mem_univ,true_and]
  apply decide_eq_decide.mpr
  have hd : (0:ℚ)<p.2.1.2.val := by exact_mod_cast h.md_pos
  have hp : (0:ℚ)<(b i).val := by exact_mod_cast hbp i
  rw [h.m_eq,heb,div_lt_div_iff₀ hd hp]
  simp only [one_mul]
  change p.2.1.1.val*(b i).val<p.2.1.2.val ↔ _
  exact_mod_cast (Iff.rfl : p.2.1.1.val*(b i).val<p.2.1.2.val ↔ _)
end RawBudget
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace RawBox
abbrev Data := W × List W × List W
noncomputable def width : Code Data W := fst
noncomputable def lower : Code Data (List W) := snd ≫ₚ fst
noncomputable def upper : Code Data (List W) := snd ≫ₚ snd
noncomputable def withFloor : Code (Data × List W) Data :=
  (fst ≫ₚ width) ⋏ₚ snd ⋏ₚ (fst ≫ₚ upper)
noncomputable def withCeiling : Code (Data × List W) Data :=
  (fst ≫ₚ width) ⋏ₚ (fst ≫ₚ lower) ⋏ₚ snd
noncomputable def clip : Code (Data × List W) (List W) :=
  ((fst ≫ₚ upper) ⋏ₚ (((fst ≫ₚ lower) ⋏ₚ snd) ≫ₚ Array.max)) ≫ₚ Array.min
noncomputable def midpoint : Code Data (List W) := (lower ⋏ₚ upper) ≫ₚ Array.average
noncomputable def averageClipped : Code (Data × List W × List W) (List W) :=
  (fst ⋏ₚ (snd ≫ₚ Array.average)) ≫ₚ clip
noncomputable def centered : Code (W × List W) Data :=
  (fst ≫ₚ Word.double) ⋏ₚ
    (((fst ≫ₚ Word.neg) ⋏ₚ snd) ≫ₚ Array.translate) ⋏ₚ (Code.id ≫ₚ Array.translate)
noncomputable def capLow : Code (Data × W) Data :=
  snd ⋏ₚ (fst ≫ₚ lower) ⋏ₚ
    (((fst ≫ₚ upper) ⋏ₚ ((snd ⋏ₚ (fst ≫ₚ lower)) ≫ₚ Array.translate)) ≫ₚ Array.min)
noncomputable def capHigh : Code (Data × W) Data :=
  snd ⋏ₚ (((fst ≫ₚ lower) ⋏ₚ (((snd ≫ₚ Word.neg) ⋏ₚ (fst ≫ₚ upper)) ≫ₚ Array.translate)) ≫ₚ Array.max) ⋏ₚ
    (fst ≫ₚ upper)
noncomputable def smallVector : Code (RawBudget.Data × Data) (List W) :=
  ((fst ≫ₚ RawBudget.smallMask) ⋏ₚ (snd ≫ₚ upper) ⋏ₚ (snd ≫ₚ lower)) ≫ₚ Array.choose
noncomputable def dividedWidth : Code (Data × Count) W := ((fst ≫ₚ width) ⋏ₚ snd) ≫ₚ Word.shiftRight
noncomputable def remainderWidth : Code (Data × Count) W :=
  ((fst ≫ₚ width) ⋏ₚ dividedWidth) ≫ₚ Word.sub
noncomputable def movedFloor : Code (Data × List W × W) Bool :=
  ((snd ≫ₚ snd) ⋏ₚ (((snd ≫ₚ fst) ⋏ₚ (fst ≫ₚ lower)) ≫ₚ Array.sub)) ≫ₚ Array.anyLE
noncomputable def movedCeiling : Code (Data × List W × W) Bool :=
  ((snd ≫ₚ snd) ⋏ₚ (((fst ≫ₚ upper) ⋏ₚ (snd ≫ₚ fst)) ≫ₚ Array.sub)) ≫ₚ Array.anyLE

structure Rep {n B : ℕ} (I : SolveBox n B) (b : Data) : Prop where
  width : b.1.val=I.width
  lower : VectorRep I.a b.2.1
  upper : VectorRep I.b b.2.2

theorem floor_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    (v : BoxVector I) {vs : List W} (hv : VectorRep v.val vs) :
    Rep (I.withFloor v) (withFloor (b,vs)) := ⟨h.width,hv,h.upper⟩
theorem ceiling_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    (v : BoxVector I) {vs : List W} (hv : VectorRep v.val vs) :
    Rep (I.withCeiling v) (withCeiling (b,vs)) := ⟨h.width,h.lower,hv⟩

theorem clip_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    VectorRep (MeanPayoff.clip I.a I.b v) (clip (b,vs)) := by
  exact Array.zip_rep Word.min Min.min (fun _ _ => Word.min_val _ _) h.upper
    (Array.zip_rep Word.max Max.max (fun _ _ => Word.max_val _ _) h.lower hv)

theorem midpoint_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b) :
    VectorRep I.midpoint.val (midpoint b) := by
  exact Array.zip_rep Word.average (fun a b => (a+b)/2) (fun _ _ => Word.average_val _ _) h.lower h.upper

theorem average_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {v w : Fin n → ℤ} {vs ws : List W} (hv : VectorRep v vs) (hw : VectorRep w ws) :
    VectorRep (I.averageClipped v w).val (averageClipped (b,vs,ws)) := by
  exact clip_rep h (Array.zip_rep Word.average (fun a b => (a+b)/2)
    (fun _ _ => Word.average_val _ _) hv hw)

theorem centered_rep {n B : ℕ} (v : Fin n → ℤ) {vs : List W} (hv : VectorRep v vs)
    {A : ℕ} (hA : 0<A) (hB : 2*A≤B) (a : W) (ha : a.val=A) :
    Rep (SolveBox.centered v A hA hB) (centered (a,vs)) := by
  refine ⟨?_,?_,?_⟩
  · simp [centered,Word.double_val,ha,SolveBox.centered]
  · convert Array.translate_rep hv (Word.neg a) using 1 <;> try rfl
    funext i
    simp [SolveBox.centered,Word.neg_val,ha]
    ring
  · convert Array.translate_rep hv a using 1 <;> try rfl
    funext i
    simp [SolveBox.centered,ha,add_comm]

theorem capLow_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {C : ℕ} (hC : 0<C) (hCI : C≤I.width) (c : W) (hc : c.val=C) :
    Rep (I.capLow C hC hCI) (capLow (b,c)) := by
  refine ⟨hc,h.lower,?_⟩
  convert Array.zip_rep Word.min Min.min (fun _ _ => Word.min_val _ _) h.upper
    (Array.translate_rep h.lower c) using 1 <;> try rfl
  funext i
  simp [SolveBox.capLow,hc,add_comm]

theorem capHigh_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {C : ℕ} (hC : 0<C) (hCI : C≤I.width) (c : W) (hc : c.val=C) :
    Rep (I.capHigh C hC hCI) (capHigh (b,c)) := by
  refine ⟨hc,?_,h.upper⟩
  convert Array.zip_rep Word.max Max.max (fun _ _ => Word.max_val _ _) h.lower
    (Array.translate_rep h.upper (Word.neg c)) using 1 <;> try rfl
  funext i
  simp [SolveBox.capHigh,Word.neg_val,hc,sub_eq_neg_add]

theorem smallVector_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {P : Budgets n} {p : RawBudget.Data} (hp : RawBudget.Rep P p) :
    VectorRep (I.smallVector P).val (smallVector (p,b)) := by
  convert Array.choose_rep (RawBudget.smallMask_eq hp) h.upper h.lower using 1 <;> try rfl
  funext i
  simp [SolveBox.smallVector,smallRankAnswer]

theorem dividedWidth_eq {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b) (c : Count) :
    (dividedWidth (b,c)).val=(I.width:ℤ)/(2^c.length) := by
  simp [dividedWidth,Word.shiftRight_val,width,h.width]

theorem dividedWidth_nat {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    (c : Count) (d : ℕ) (hc : 2^c.length=d) :
    (dividedWidth (b,c)).val=(I.width/d:ℕ) := by
  rw [dividedWidth_eq h]
  norm_cast
  rw [hc]

theorem remainderWidth_nat {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    (c : Count) (d : ℕ) (hc : 2^c.length=d) :
    (remainderWidth (b,c)).val=(I.width-I.width/d:ℕ) := by
  change (Word.sub (b.1,dividedWidth (b,c))).val=_
  rw [Word.sub_val,h.width,dividedWidth_nat h c d hc,Int.ofNat_sub (Nat.div_le_self _ _)]

theorem movedFloor_eq {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) (d : W) :
    movedFloor (b,vs,d)=decide (∃ i, d.val≤v i-I.a i) := by
  exact Array.anyLE_eq d (Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) hv h.lower)
theorem movedCeiling_eq {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) (d : W) :
    movedCeiling (b,vs,d)=decide (∃ i, d.val≤I.b i-v i) := by
  exact Array.anyLE_eq d (Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) h.upper hv)
end RawBox
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff

theorem box_iterate_fixed {n : ℕ} (F : Vec (Fin n) → Vec (Fin n)) (hF : Monotone F)
    (a b : Vec (Fin n)) (hab : a≤b) (p : Vec (Fin n)) (_hp : InBox a b p)
    (hi : p≤boxStep F a b p) (t : ℕ) (ht : volume b p≤t) :
    boxStep F a b ((boxStep F a b)^[t] p)=(boxStep F a b)^[t] p := by
  by_cases heq : boxStep F a b p=p
  · have hit : ∀ k, (boxStep F a b)^[k] p=p := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply',ih,heq]
    rw [hit,heq]
  · have hq := boxStep_in_box F hab p
    have hnext := boxStep_mono hF a b hi
    have hv := volume_decreases hi hq.2 (Ne.symm heq)
    cases t with
    | zero => omega
    | succ t =>
      rw [Function.iterate_succ_apply]
      exact box_iterate_fixed F hF a b hab (boxStep F a b p) hq hnext t (by omega)
termination_by volume b p

theorem SolveBox.volume_bound {n B : ℕ} (I : SolveBox n B) : volume I.b I.a≤n*I.width := by
  unfold volume
  calc
    ∑ i : Fin n, (I.b i-I.a i).toNat ≤ ∑ _i : Fin n, I.width := by
      apply Finset.sum_le_sum
      intro i _
      exact Int.toNat_le.mpr (by exact_mod_cast I.width_bound i)
    _ = n*I.width := by simp

theorem SolveBox.iterate_exact (G : Game) {B : ℕ} (I : SolveBox G.n B)
    (t : ℕ) (ht : G.n*I.width≤t) :
    (boxStep (operator G) I.a I.b)^[t] I.a = (I.exactVector G).val := by
  have hf := box_iterate_fixed (operator G) (operator_laws G).mono I.a I.b I.ordered I.a
    ⟨le_rfl,I.ordered⟩ (boxStep_in_box (operator G) I.ordered I.a).1 t (I.volume_bound.trans ht)
  have hs := (fixed_iff_comparisons (operator G) I.ordered).mp hf
  exact le_antisymm (box_comparison G hs.1 (basic_spec G I.a I.b I.ordered).2.1)
    (box_comparison G (basic_spec G I.a I.b I.ordered).1 hs.2)
end MeanPayoff
end

end OAI
