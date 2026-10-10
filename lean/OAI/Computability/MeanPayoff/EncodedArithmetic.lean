import OAI.Computability.MeanPayoff.EncodedPrograms

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

theorem take_size {α : Type} [Encoding α] (xs : List α) (k : ℕ) :
    treeSize (encode (xs.take k)) ≤ treeSize (encode xs) := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => exact treeSize_pos _
    | succ k =>
      change treeSize (listTree encode ((x::xs).take (k+1))) ≤ treeSize (listTree encode (x::xs))
      simp only [List.take_succ_cons,listTree,treeSize_pair]
      have h := ih k
      change treeSize (listTree encode (xs.take k)) ≤ treeSize (listTree encode xs) at h
      omega

namespace Word
@[simp] theorem add_length (x y : W) : (add (x,y)).digits.length=Max.max x.digits.length y.digits.length+1 :=
  SignedBits.add_length _ _ _ _ _
@[simp] theorem neg_length (x : W) : (neg x).digits.length=Max.max x.digits.length 1+1 := by
  change (SignedBits.add _ _ _ _ _).digits.length=_
  rw [SignedBits.add_length]
  simp [SignedBits.Word.complement,Negate.one]
@[simp] theorem half_length (x : W) : (half x).digits.length=x.digits.length-1 := List.length_tail
@[simp] theorem double_length (x : W) : (double x).digits.length=x.digits.length+1 := Multiply.double_length _

theorem addFold_length (a : W) (xs : List W) :
    (Fold.fold add.eval a xs).digits.length ≤ a.digits.length+(xs.map (fun x => x.digits.length+1)).sum := by
  induction xs generalizing a with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    have h := ih (add (a,x))
    change (Fold.fold add.eval (add (a,x)) xs).digits.length ≤ _
    simp only [List.map_cons,List.sum_cons]
    rw [add_length] at h
    omega

theorem digitSum_le_size (xs : List W) :
    (xs.map (fun x => x.digits.length+1)).sum ≤ treeSize (encode xs) := by
  induction xs with
  | nil => simp []
  | cons x xs ih =>
    have h := digits_le_wordSize x
    change _ ≤ treeSize (listTree wordData (x::xs))
    rw [listTree,treeSize_pair]
    simp only [List.map_cons,List.sum_cons]
    change _ ≤ treeSize (listTree wordData xs) at ih
    omega

noncomputable def addFold : Code (W × List W) W := foldPrefix add 10 1 (by
  intro a xs k hk
  have hl := addFold_length a (xs.take k)
  have hs := digitSum_le_size (xs.take k)
  have ht : treeSize (encode (xs.take k)) ≤ treeSize (encode xs) := by
    exact take_size xs k
  have ha := digits_le_wordSize a
  have hh := wordSize_bound (Fold.fold add.eval a (xs.take k))
  simp only [pow_one]
  change treeSize (wordData (Fold.fold add.eval a (xs.take k))) ≤ 10*(treeSize (product wordData (listTree wordData) (a,xs))+1)
  rw [product,treeSize_pair]
  change (List.map (fun x => x.digits.length+1) (xs.take k)).sum ≤ treeSize (listTree wordData (xs.take k)) at hs
  change treeSize (listTree wordData (xs.take k)) ≤ treeSize (listTree wordData xs) at ht
  dsimp only [Prod.fst,Prod.snd]
  nlinarith)

noncomputable def sum : Code (List W) W := (const Median.zeroWord ⋏ₚ Code.id) ≫ₚ addFold

theorem addFold_val (a : W) (xs : List W) :
    (addFold (a,xs)).val=a.val+(xs.map SignedBits.Word.val).sum := by
  change (Fold.fold add.eval a xs).val=_
  induction xs generalizing a with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    change (Fold.fold add.eval (add (a,x)) xs).val=_
    have h := ih (add (a,x))
    simp only [List.map_cons,List.sum_cons] at *
    rw [add_val] at h
    omega
@[simp] theorem sum_val (xs : List W) : (sum xs).val=(xs.map SignedBits.Word.val).sum := by
  change (addFold (Median.zeroWord,xs)).val=_
  rw [addFold_val]
  change 0+_=_
  omega

noncomputable def shiftStep : Code (W × Unit) W := fst ≫ₚ half
noncomputable def shiftRight : Code (W × Count) W := fold shiftStep (by
  intro w u
  change treeSize (wordData (Halve.halve w)) ≤ treeSize (wordData w)+treeSize (Median.unitData u)+1
  cases w with
  | mk s ds =>
    cases ds with
    | nil =>
      simp only [Halve.halve,wordData,listData,treeSize_pair,List.tail_nil]
      omega
    | cons b bs =>
      simp only [Halve.halve,wordData,listData,List.tail_cons,treeSize_pair]
      omega)

theorem shiftRight_val (w : W) (c : Count) : (shiftRight (w,c)).val=w.val/(2^c.length) := by
  change (Fold.fold shiftStep.eval w c).val=_
  induction c generalizing w with
  | nil => simp [Fold.fold]
  | cons u cs ih =>
    change (Fold.fold shiftStep.eval (half w) cs).val=_
    rw [ih,half_val,Int.ediv_ediv]
    simp only [List.length_cons,pow_succ]
    norm_num
    rw [mul_comm]
end Word

namespace Counter
noncomputable def inc : Code Count Count := (const () ⋏ₚ Code.id) ≫ₚ cons
noncomputable def step : Code (W × Unit) W := (fst ⋏ₚ const Negate.one) ≫ₚ Word.add
noncomputable def word : Code Count W := map (const Negate.one) ≫ₚ Word.sum
@[simp] theorem word_val (xs : Count) : (word xs).val=xs.length := by
  simp [word,Code.const,List.sum_replicate]
noncomputable def add : Code (Count × Count) Count := append
noncomputable def mul : Code (Count × Count) Count := envMap (fst : Code (Count × Unit) Count) ≫ₚ flatten
@[simp] theorem add_length (a b : Count) : (add (a,b)).length=a.length+b.length := by simp [add]
@[simp] theorem mul_length (a b : Count) : (mul (a,b)).length=a.length*b.length := by
  simp [mul,List.length_flatten,List.sum_replicate,Nat.mul_comm]
end Counter
end MeanPayoff.TreeDevice.Certified
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

def VectorRep {n : ℕ} (v : Fin n → ℤ) (xs : List W) : Prop :=
  ∃ ws : Fin n → W, xs=List.ofFn ws ∧ ∀ i, (ws i).val=v i

def MaskRep {n : ℕ} (H : Finset (Fin n)) (xs : List Bool) : Prop :=
  xs=List.ofFn (fun i => decide (i∈H))

namespace Word
noncomputable def constant {α : Type} [Encoding α] (z : ℤ) : Code α W := const (EdgeRead.encodedWord z)
@[simp] theorem constant_val {α : Type} [Encoding α] (z : ℤ) (x : α) :
    (constant z x).val=z := EdgeRead.encodedWord_val z
end Word

namespace Array
def zero : W := Median.zeroWord
noncomputable def add : Code (List W × List W) (List W) := zip zero zero Word.add
noncomputable def sub : Code (List W × List W) (List W) := zip zero zero Word.sub
noncomputable def min : Code (List W × List W) (List W) := zip zero zero Word.min
noncomputable def max : Code (List W × List W) (List W) := zip zero zero Word.max
noncomputable def average : Code (List W × List W) (List W) := zip zero zero Word.average
noncomputable def mul : Code (List W × List W) (List W) := zip zero zero Word.mul
noncomputable def lt : Code (List W × List W) (List Bool) := zip zero zero Word.lt
noncomputable def le : Code (List W × List W) (List Bool) := zip zero zero Word.le
noncomputable def scale : Code (W × List W) (List W) := envMap Word.mul
noncomputable def translate : Code (W × List W) (List W) := envMap Word.add
noncomputable def complement : Code (List Bool) (List Bool) := map Code.not
noncomputable def mask : Code (List W × List Bool) (List W) :=
  zip zero false (Code.branch snd fst (Word.constant 0))
noncomputable def doubleOn : Code (List W × List Bool) (List W) :=
  zip zero false (Code.branch snd (fst ≫ₚ Word.double) fst)

theorem zip_ofFn {α β γ : Type} (f : α × β → γ) (b : β) {n : ℕ}
    (as : Fin n → α) (bs : Fin n → β) :
    Zip.zip f b (List.ofFn as) (List.ofFn bs)=List.ofFn (fun i => f (as i,bs i)) := by
  induction n with
  | zero => simp [List.ofFn_zero,Zip.zip]
  | succ n ih => simp [List.ofFn_succ,Zip.zip,ih]

theorem zip_rep {n : ℕ} (f : Code (W × W) W) (g : ℤ → ℤ → ℤ)
    (hf : ∀ w v, (f (w,v)).val=g w.val v.val)
    {x y : Fin n → ℤ} {xs ys : List W} (hx : VectorRep x xs) (hy : VectorRep y ys) :
    VectorRep (fun i => g (x i) (y i)) (zip zero zero f (xs,ys)) := by
  obtain ⟨ws,rfl,hw⟩ := hx
  obtain ⟨vs,rfl,hv⟩ := hy
  refine ⟨fun i => f (ws i,vs i),?_,?_⟩
  · exact zip_ofFn f.eval zero ws vs
  · intro i
    rw [hf,hw,hv]
end Array

namespace RawBudget

abbrev Data := (W × W) × (W × W) × List W × List W
noncomputable def k : Code Data (W × W) := fst
noncomputable def m : Code Data (W × W) := snd ≫ₚ fst
noncomputable def alpha : Code Data (List W) := snd ≫ₚ snd ≫ₚ fst
noncomputable def beta : Code Data (List W) := snd ≫ₚ snd ≫ₚ snd
noncomputable def kn : Code Data W := k ≫ₚ fst
noncomputable def kd : Code Data W := k ≫ₚ snd
noncomputable def mn : Code Data W := m ≫ₚ fst
noncomputable def md : Code Data W := m ≫ₚ snd
noncomputable def times (r : ℤ) : Code W W := (Code.id ⋏ₚ Word.constant r) ≫ₚ Word.mul
noncomputable def shrink (r : ℤ) : Code (W × W) (W × W) :=
  (fst ≫ₚ times r) ⋏ₚ (snd ≫ₚ times 5)
noncomputable def reduceK : Code Data Data := (k ≫ₚ shrink 4) ⋏ₚ m ⋏ₚ alpha ⋏ₚ beta
noncomputable def reduceM : Code Data Data := k ⋏ₚ (m ≫ₚ shrink 4) ⋏ₚ alpha ⋏ₚ beta
noncomputable def reweightK : Code (Data × List Bool) Data :=
  (fst ≫ₚ k ≫ₚ shrink 3) ⋏ₚ (fst ≫ₚ m) ⋏ₚ
    (((fst ≫ₚ alpha) ⋏ₚ snd) ≫ₚ Array.doubleOn) ⋏ₚ (fst ≫ₚ beta)
noncomputable def reweightM : Code (Data × List Bool) Data :=
  (fst ≫ₚ k) ⋏ₚ (fst ≫ₚ m ≫ₚ shrink 3) ⋏ₚ (fst ≫ₚ alpha) ⋏ₚ
    (((fst ≫ₚ beta) ⋏ₚ snd) ≫ₚ Array.doubleOn)
noncomputable def density : Code Data (List W) := (alpha ⋏ₚ beta) ≫ₚ Array.mul
noncomputable def total : Code Data W := density ≫ₚ Word.sum
noncomputable def parameterNumerator : Code Data W := (((kn ⋏ₚ mn) ≫ₚ Word.mul) ⋏ₚ total) ≫ₚ Word.mul
noncomputable def parameterDenominator : Code Data W := (kd ⋏ₚ md) ≫ₚ Word.mul
noncomputable def small : Code Data Bool := (parameterNumerator ⋏ₚ parameterDenominator) ≫ₚ Word.lt
noncomputable def measureLarge : Code (Data × List Bool) Bool :=
  ((fst ≫ₚ total) ⋏ₚ ((((fst ≫ₚ density) ⋏ₚ snd) ≫ₚ Array.mask ≫ₚ Word.sum) ≫ₚ Word.double)) ≫ₚ Word.lt
noncomputable def smallMask : Code Data (List Bool) :=
  (((mn ⋏ₚ beta) ≫ₚ Array.scale) ⋏ₚ ((md ⋏ₚ beta) ≫ₚ envMap (fst : Code (W × W) W))) ≫ₚ Array.lt

structure Rep {n : ℕ} (P : Budgets n) (p : Data) : Prop where
  kn_pos : 0<p.1.1.val
  kd_pos : 0<p.1.2.val
  mn_pos : 0<p.2.1.1.val
  md_pos : 0<p.2.1.2.val
  k_eq : P.k=(p.1.1.val:ℚ)/(p.1.2.val:ℚ)
  m_eq : P.m=(p.2.1.1.val:ℚ)/(p.2.1.2.val:ℚ)
  coords : ∃ a b : Fin n → W,
    p.2.2.1=List.ofFn a ∧ p.2.2.2=List.ofFn b ∧
    (∀ i, 0<(a i).val) ∧ (∀ i, 0<(b i).val) ∧
    (∀ i, P.alpha i=1/((a i).val:ℚ)) ∧ (∀ i, P.beta i=1/((b i).val:ℚ))

@[simp] theorem times_val (r : ℤ) (w : W) : (times r w).val=w.val*r := by simp [times]

theorem shrink_fst (r : ℤ) (p : W × W) : ((shrink r p).1).val=p.1.val*r := by simp [shrink]
theorem shrink_snd (r : ℤ) (p : W × W) : ((shrink r p).2).val=p.2.val*5 := by simp [shrink]

theorem reduceK_rep {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    Rep P.reduceK (reduceK p) := by
  rcases h with ⟨hkn,hkd,hmn,hmd,hk,hm,hcoords⟩
  refine ⟨?_,?_,hmn,hmd,?_,hm,hcoords⟩
  · change 0<((shrink 4 p.1).1).val
    rw [shrink_fst]
    omega
  · change 0<((shrink 4 p.1).2).val
    rw [shrink_snd]
    omega
  · change (4/5:ℚ)*P.k=(((shrink 4 p.1).1).val:ℚ)/(((shrink 4 p.1).2).val:ℚ)
    rw [hk,shrink_fst,shrink_snd]
    push_cast
    ring

theorem reduceM_rep {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    Rep P.reduceM (reduceM p) := by
  rcases h with ⟨hkn,hkd,hmn,hmd,hk,hm,hcoords⟩
  refine ⟨hkn,hkd,?_,?_,hk,?_,hcoords⟩
  · change 0<((shrink 4 p.2.1).1).val
    rw [shrink_fst]
    omega
  · change 0<((shrink 4 p.2.1).2).val
    rw [shrink_snd]
    omega
  · change (4/5:ℚ)*P.m=(((shrink 4 p.2.1).1).val:ℚ)/(((shrink 4 p.2.1).2).val:ℚ)
    rw [hm,shrink_fst,shrink_snd]
    push_cast
    ring

theorem reweightK_rep {n : ℕ} {P : Budgets n} {p : Data} {H : Finset (Fin n)} {hs : List Bool}
    (h : Rep P p) (hH : MaskRep H hs) : Rep (P.reweightK H) (reweightK (p,hs)) := by
  rcases h with ⟨hkn,hkd,hmn,hmd,hk,hm,a,b,ha,hb,hap,hbp,hea,heb⟩
  refine ⟨?_,?_,hmn,hmd,?_,hm,?_⟩
  · change 0<((shrink 3 p.1).1).val
    rw [shrink_fst]
    omega
  · change 0<((shrink 3 p.1).2).val
    rw [shrink_snd]
    omega
  · change (3/5:ℚ)*P.k=(((shrink 3 p.1).1).val:ℚ)/(((shrink 3 p.1).2).val:ℚ)
    rw [hk,shrink_fst,shrink_snd]
    push_cast
    ring
  · let a' : Fin n → W := fun i => if i∈H then Word.double (a i) else a i
    refine ⟨a',b,?_,hb,?_,hbp,?_,heb⟩
    · change Zip.zip _ _ p.2.2.1 hs=List.ofFn a'
      rw [ha,hH,Array.zip_ofFn]
      congr 1
      funext i
      simp [a',Code.branch,Code.comp,Code.fst,Code.snd]
    · intro i
      dsimp [a']
      split_ifs
      · rw [Word.double_val]
        have := hap i
        omega
      · exact hap i
    · intro i
      change halve P.alpha H i=1/((a' i).val:ℚ)
      unfold halve a'
      split_ifs <;> simp [hea,Word.double_val] ; ring

theorem reweightM_rep {n : ℕ} {P : Budgets n} {p : Data} {H : Finset (Fin n)} {hs : List Bool}
    (h : Rep P p) (hH : MaskRep H hs) : Rep (P.reweightM H) (reweightM (p,hs)) := by
  rcases h with ⟨hkn,hkd,hmn,hmd,hk,hm,a,b,ha,hb,hap,hbp,hea,heb⟩
  refine ⟨hkn,hkd,?_,?_,hk,?_,?_⟩
  · change 0<((shrink 3 p.2.1).1).val
    rw [shrink_fst]
    omega
  · change 0<((shrink 3 p.2.1).2).val
    rw [shrink_snd]
    omega
  · change (3/5:ℚ)*P.m=(((shrink 3 p.2.1).1).val:ℚ)/(((shrink 3 p.2.1).2).val:ℚ)
    rw [hm,shrink_fst,shrink_snd]
    push_cast
    ring
  · let b' : Fin n → W := fun i => if i∈H then Word.double (b i) else b i
    refine ⟨a,b',ha,?_,hap,?_,hea,?_⟩
    · change Zip.zip _ _ p.2.2.2 hs=List.ofFn b'
      rw [hb,hH,Array.zip_ofFn]
      congr 1
      funext i
      simp [b',Code.branch,Code.comp,Code.fst,Code.snd]
    · intro i
      dsimp [b']
      split_ifs
      · rw [Word.double_val]
        have := hbp i
        omega
      · exact hbp i
    · intro i
      change halve P.beta H i=1/((b' i).val:ℚ)
      unfold halve b'
      split_ifs <;> simp [heb,Word.double_val] ; ring

theorem density_cast {n : ℕ} {P : Budgets n} {a b : Fin n → W}
    (ha : ∀ i, P.alpha i=1/((a i).val:ℚ)) (hb : ∀ i, P.beta i=1/((b i).val:ℚ)) (i : Fin n) :
    P.density i=((a i).val:ℚ)*((b i).val:ℚ) := by
  simp [Budgets.density,ha,hb,one_div,mul_inv_rev,mul_comm]

theorem total_eq {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    ((total p).val:ℚ)=P.totalDensity := by
  obtain ⟨a,b,ha,hb,_,_,hea,heb⟩ := h.coords
  change ((Word.sum (Array.mul (p.2.2.1,p.2.2.2))).val:ℚ)=_
  rw [ha,hb]
  change ((Word.sum (Zip.zip _ _ (List.ofFn a) (List.ofFn b))).val:ℚ)=_
  rw [Array.zip_ofFn,Word.sum_val]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,Word.mul_val]
  push_cast
  unfold Budgets.totalDensity mass
  apply Finset.sum_congr rfl
  intro i _
  exact (density_cast hea heb i).symm

theorem masked_eq {n : ℕ} {P : Budgets n} {p : Data} {H : Finset (Fin n)} {hs : List Bool}
    (h : Rep P p) (hH : MaskRep H hs) :
    ((Word.sum (Array.mask (density p,hs))).val:ℚ)=mass P.density H := by
  obtain ⟨a,b,ha,hb,_,_,hea,heb⟩ := h.coords
  change ((Word.sum (Zip.zip _ _ (Zip.zip _ _ p.2.2.1 p.2.2.2) hs)).val:ℚ)=_
  rw [ha,hb,hH,Array.zip_ofFn,Array.zip_ofFn,Word.sum_val]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rw [Int.cast_sum]
  unfold mass
  calc
    _ = ∑ i : Fin n, if i∈H then P.density i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      change ((if decide (i∈H) then Word.mul (a i,b i) else Word.constant 0 (Word.mul (a i,b i),decide (i∈H))).val:ℚ)=_
      by_cases hi : i∈H
      · simp only [hi,decide_true,↓reduceIte,Word.mul_val,Int.cast_mul]
        exact (density_cast hea heb i).symm
      · simp [hi]
    _ = _ := by simp []

theorem small_eq {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    small p=decide (P.parameter<1) := by
  change Word.lt (parameterNumerator p,parameterDenominator p)=_
  rw [Word.lt_eval]
  apply decide_eq_decide.mpr
  have hk : (((kn p).val:ℤ):ℚ)=(p.1.1.val:ℚ) := rfl
  have ht := total_eq h
  have hd : (0:ℚ)<p.1.2.val*p.2.1.2.val := by
    exact mul_pos (by exact_mod_cast h.kd_pos) (by exact_mod_cast h.md_pos)
  have he : P.parameter=
      ((parameterNumerator p).val:ℚ)/((parameterDenominator p).val:ℚ) := by
    change P.k*P.m*P.totalDensity=_
    simp only [parameterNumerator,parameterDenominator,comp_eval,pair_eval,Word.mul_val,Int.cast_mul]
    rw [← ht,h.k_eq,h.m_eq]
    change _=(p.1.1.val:ℚ)*p.2.1.1.val*(total p).val/((p.1.2.val:ℚ)*p.2.1.2.val)
    ring
  rw [he,div_lt_one (by
    change (0:ℚ)<((Word.mul (p.1.2,p.2.1.2)).val:ℚ)
    rw [Word.mul_val,Int.cast_mul]
    exact hd)]
  exact_mod_cast (Iff.rfl : (parameterNumerator p).val<(parameterDenominator p).val ↔ _)

theorem measureLarge_eq {n : ℕ} {P : Budgets n} {p : Data} {H : Finset (Fin n)} {hs : List Bool}
    (hn : 0<n) (h : Rep P p) (hH : MaskRep H hs) :
    measureLarge (p,hs)=decide ((1/2:ℚ)<P.measure H) := by
  change Word.lt (total p,Word.double (Word.sum (Array.mask (density p,hs))))=_
  rw [Word.lt_eval,Word.double_val]
  apply decide_eq_decide.mpr
  have ht := total_eq h
  have hm := masked_eq h hH
  have hp := P.totalDensity_pos hn
  have he : (1/2:ℚ)<P.measure H ↔ P.totalDensity<2*mass P.density H := by
    unfold Budgets.measure
    rw [lt_div_iff₀ hp]
    constructor <;> intro hh <;> linarith
  rw [he,← ht,← hm]
  exact_mod_cast (Iff.rfl : (total p).val<2*(Word.sum (Array.mask (density p,hs))).val ↔ _)
end RawBudget
end MeanPayoff.TreeDevice.Certified
end

end OAI
