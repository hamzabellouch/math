import OAI.Computability.MeanPayoff.RawLabels

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

namespace Word
@[simp] theorem sub_length (x y : W) : (sub (x,y)).digits.length = Max.max x.digits.length (Max.max y.digits.length 1+1)+1 := by
  change (add (x,neg y)).digits.length = _
  rw [add_length,neg_length]
@[simp] theorem average_length (x y : W) : (average (x,y)).digits.length=Max.max x.digits.length y.digits.length := by
  change (half (add (x,y))).digits.length = _
  simp only [half_length,add_length,Nat.add_sub_cancel]
theorem unsignedMul_length (x y : W) : (unsignedMul (x,y)).digits.length≤x.digits.length+2*y.digits.length := by
  have h := Multiply.fold_length (x,Median.zeroWord) y.digits.reverse
  change (Multiply.multiply (x,y.digits)).digits.length≤_
  simpa only [Multiply.multiply,List.length_reverse,show Median.zeroWord.digits.length=0 from rfl,zero_max] using h
theorem mul_length (x y : W) : (mul (x,y)).digits.length≤x.digits.length+2*y.digits.length+6 := by
  change (if y.sign then neg (unsignedMul (x,neg y)) else unsignedMul (x,y)).digits.length≤_
  split
  · have h := unsignedMul_length x (neg y)
    rw [neg_length] at h
    rw [neg_length]
    omega
  · have h := unsignedMul_length x y
    omega
theorem shiftRight_length (x : W) (c : Count) : (shiftRight (x,c)).digits.length≤x.digits.length := by
  change (Fold.fold shiftStep.eval x c).digits.length≤_
  induction c generalizing x with
  | nil => exact le_rfl
  | cons u cs ih =>
    have h := ih (half x)
    change (Fold.fold shiftStep.eval (half x) cs).digits.length≤_
    exact h.trans (by rw [half_length]; omega)
end Word
namespace Array
 theorem Bounded.mono {xs : List W} {M N : ℕ} (h : Bounded xs M) (hm : M≤N) : Bounded xs N :=
  fun _ hw => (h _ hw).trans hm
 theorem Bounded.nil (M : ℕ) : Bounded [] M := by simp [Bounded]
 theorem Bounded.cons {x : W} {xs : List W} {M : ℕ} (hx : x.digits.length≤M) (hs : Bounded xs M) : Bounded (x::xs) M := by
  intro y hy; rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact hs y hy
 theorem bounded_zip_general {xs ys : List W} {M N P : ℕ} (hx : Bounded xs M) (hy : Bounded ys N)
    (f : Code (W×W) W) (hf : ∀ x y, x.digits.length≤M → y.digits.length≤N → (f (x,y)).digits.length≤P) :
    Bounded (zip zero zero f (xs,ys)) P := by
  change Bounded (Zip.zip f.eval zero xs ys) P
  induction xs generalizing ys with
  | nil => exact Bounded.nil _
  | cons x xs ih =>
    have hxs : Bounded xs M := fun w hw => hx w (List.mem_cons_of_mem _ hw)
    cases ys with
    | nil =>
      exact Bounded.cons (hf x zero (hx x (by simp)) (Nat.zero_le _)) (ih hxs (Bounded.nil _))
    | cons y ys =>
      exact Bounded.cons (hf x y (hx x (by simp)) (hy y (by simp)))
        (ih hxs (fun w hw => hy w (List.mem_cons_of_mem _ hw)))
 theorem add_bound {xs ys : List W} {M : ℕ} (hx : Bounded xs M) (hy : Bounded ys M) : Bounded (add (xs,ys)) (M+1) :=
  bounded_zip_general hx hy Word.add (by intro x y hx hy; rw [Word.add_length]; omega)
 theorem sub_bound {xs ys : List W} {M : ℕ} (hx : Bounded xs M) (hy : Bounded ys M) : Bounded (sub (xs,ys)) (M+3) :=
  bounded_zip_general hx hy Word.sub (by intro x y hx hy; rw [Word.sub_length]; omega)
 theorem average_bound {xs ys : List W} {M : ℕ} (hx : Bounded xs M) (hy : Bounded ys M) : Bounded (average (xs,ys)) M :=
  bounded_zip_general hx hy Word.average (by intro x y hx hy; rw [Word.average_length]; omega)
 theorem min_bound {xs ys : List W} {M : ℕ} (hx : Bounded xs M) (hy : Bounded ys M) : Bounded (min (xs,ys)) M :=
  bounded_zip hx hy Word.min EdgeScan.low_mem
 theorem max_bound {xs ys : List W} {M : ℕ} (hx : Bounded xs M) (hy : Bounded ys M) : Bounded (max (xs,ys)) M :=
  bounded_zip hx hy Word.max EdgeScan.high_mem
 theorem translate_bound {x : W} {xs : List W} {M : ℕ} (hx : x.digits.length≤M) (hs : Bounded xs M) : Bounded (translate (x,xs)) (M+1) := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  change (Word.add (x,v)).digits.length≤M+1
  rw [Word.add_length]
  have := hs v hv
  omega
 theorem Bounded.headD {xs : List W} {M : ℕ} (h : Bounded xs M) : (xs.headD zero).digits.length≤M := by
  cases xs with
  | nil => exact Nat.zero_le _
  | cons x xs => exact h x (by simp)
 theorem Bounded.getD {xss : List (List W)} {M : ℕ} (h : ∀ xs∈xss, Bounded xs M) (i : ℕ)
    {d : List W} (hd : Bounded d M) : Bounded (xss.getD i d) M := by
  induction xss generalizing i with
  | nil => exact hd
  | cons xs xss ih =>
    cases i with
    | zero => exact h xs (by simp)
    | succ i => exact ih (fun ys hy => h ys (by simp [hy])) i
end Array
end MeanPayoff.TreeDevice.Certified

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Array
structure Small (n M : ℕ) (xs : List W) : Prop where
  length : xs.length≤n
  digits : Bounded xs M
 theorem Small.mono {n M N : ℕ} {xs : List W} (h : Small n M xs) (hm : M≤N) : Small n N xs := ⟨h.length,h.digits.mono hm⟩
 theorem Small.nil (n M : ℕ) : Small n M [] := ⟨Nat.zero_le _,Bounded.nil _⟩
 theorem Small.zip {n M : ℕ} {xs ys : List W} (hx : Small n M xs) (hy : Small n M ys)
    (f : Code (W×W) W) (hf : ∀ z, f z=z.1 ∨ f z=z.2) : Small n M (zip zero zero f (xs,ys)) :=
  ⟨(zip_length f.eval zero xs ys).le.trans hx.length,bounded_zip hx.digits hy.digits f hf⟩
 theorem Small.min {n M : ℕ} {xs ys : List W} (hx : Small n M xs) (hy : Small n M ys) : Small n M (min (xs,ys)) := hx.zip hy Word.min EdgeScan.low_mem
 theorem Small.max {n M : ℕ} {xs ys : List W} (hx : Small n M xs) (hy : Small n M ys) : Small n M (max (xs,ys)) := hx.zip hy Word.max EdgeScan.high_mem
 theorem Small.average {n M : ℕ} {xs ys : List W} (hx : Small n M xs) (hy : Small n M ys) : Small n M (average (xs,ys)) :=
  ⟨(zip_length Word.average.eval zero xs ys).le.trans hx.length,average_bound hx.digits hy.digits⟩
 theorem Small.translate {n M : ℕ} {w : W} {xs : List W} (hw : w.digits.length≤M) (hx : Small n M xs) : Small n (M+1) (translate (w,xs)) :=
  ⟨by change (xs.map _).length≤n; simpa only [List.length_map] using hx.length,translate_bound hw hx.digits⟩
 theorem Small.getD {n M : ℕ} {xss : List (List W)} (h : ∀ xs∈xss, Small n M xs) (i : ℕ)
    {d : List W} (hd : Small n M d) : Small n M (xss.getD i d) := by
  induction xss generalizing i with
  | nil => exact hd
  | cons xs xss ih => cases i with
    | zero => exact h xs (by simp)
    | succ i => exact ih (fun ys hy => h ys (by simp [hy])) i
 theorem Small.doubleOn {n M : ℕ} {xs : List W} (h : Small n M xs) (bs : List Bool) : Small n (M+1) (doubleOn (xs,bs)) := by
  refine ⟨(zip_length _ false xs bs).le.trans h.length,?_⟩
  change Bounded (Zip.zip _ false xs bs) (M+1)
  have all : ∀ xs bs, Bounded xs M → Bounded (Zip.zip (Code.branch snd (fst.comp Word.double) fst).eval false xs bs) (M+1) := by
    intro xs
    induction xs with
    | nil => intro bs _; exact Bounded.nil _
    | cons x xs ih =>
      intro bs hx
      cases bs with
      | nil =>
        apply Bounded.cons
        · exact (hx x (by simp)).trans (by omega)
        · exact ih [] (fun y hy => hx y (by simp [hy]))
      | cons b bs =>
        apply Bounded.cons
        · change (if b then Word.double x else x).digits.length≤M+1
          split
          · rw [Word.double_length]; have := hx x (by simp); omega
          · exact (hx x (by simp)).trans (by omega)
        · exact ih bs (fun y hy => hx y (by simp [hy]))
  exact all xs bs h.digits
end Array
namespace RawBudget
structure Small (n M : ℕ) (p : Data) : Prop where
  kn : p.1.1.digits.length≤M
  kd : p.1.2.digits.length≤M
  mn : p.2.1.1.digits.length≤M
  md : p.2.1.2.digits.length≤M
  alpha : Array.Small n M p.2.2.1
  beta : Array.Small n M p.2.2.2
 theorem Small.mono {n M N : ℕ} {p : Data} (h : Small n M p) (hm : M≤N) : Small n N p :=
  ⟨h.kn.trans hm,h.kd.trans hm,h.mn.trans hm,h.md.trans hm,h.alpha.mono hm,h.beta.mono hm⟩
 theorem times_length (r : ℤ) (w : W) : (times r w).digits.length≤w.digits.length+2*(EdgeRead.encodedWord r).digits.length+6 := Word.mul_length _ _
 theorem encodedWord_length_nonneg (r : ℤ) (hr : 0≤r) : (EdgeRead.encodedWord r).digits.length=(r.natAbs+1).bits.length+1 := by
  rw [EdgeRead.encodedWord,ite_eq_right (by omega)]
  change (Word.add (IntegerRead.positive _,IntegerRead.minusOne)).digits.length=_
  rw [Word.add_length]
  simp [IntegerRead.positive,IntegerRead.minusOne]
 theorem constant_short (r : ℤ) (hr : r=3 ∨ r=4 ∨ r=5) : (EdgeRead.encodedWord r).digits.length≤4 := by
  rcases hr with rfl | rfl | rfl <;> rw [encodedWord_length_nonneg _ (by omega)] <;> decide
 theorem times_short {M : ℕ} {w : W} (h : w.digits.length≤M) (r : ℤ) (hr : (EdgeRead.encodedWord r).digits.length≤4) :
    (times r w).digits.length≤M+14 := by have := times_length r w; omega
 theorem Small.reduceK {n M : ℕ} {p : Data} (h : Small n M p) : Small n (M+14) (reduceK p) := by
  refine ⟨times_short h.kn 4 (constant_short 4 (by tauto)),times_short h.kd 5 (constant_short 5 (by tauto)),h.mn.trans (by omega),h.md.trans (by omega),h.alpha.mono (by omega),h.beta.mono (by omega)⟩
 theorem Small.reduceM {n M : ℕ} {p : Data} (h : Small n M p) : Small n (M+14) (reduceM p) := by
  refine ⟨h.kn.trans (by omega),h.kd.trans (by omega),times_short h.mn 4 (constant_short 4 (by tauto)),times_short h.md 5 (constant_short 5 (by tauto)),h.alpha.mono (by omega),h.beta.mono (by omega)⟩
 theorem Small.reweightK {n M : ℕ} {p : Data} (h : Small n M p) (bs : List Bool) : Small n (M+14) (reweightK (p,bs)) := by
  refine ⟨times_short h.kn 3 (constant_short 3 (by tauto)),times_short h.kd 5 (constant_short 5 (by tauto)),h.mn.trans (by omega),h.md.trans (by omega),(h.alpha.doubleOn bs).mono (by omega),h.beta.mono (by omega)⟩
 theorem Small.reweightM {n M : ℕ} {p : Data} (h : Small n M p) (bs : List Bool) : Small n (M+14) (reweightM (p,bs)) := by
  refine ⟨h.kn.trans (by omega),h.kd.trans (by omega),times_short h.mn 3 (constant_short 3 (by tauto)),times_short h.md 5 (constant_short 5 (by tauto)),h.alpha.mono (by omega),(h.beta.doubleOn bs).mono (by omega)⟩
end RawBudget
namespace RawBox
structure Small (n M : ℕ) (b : Data) : Prop where
  width : b.1.digits.length≤M
  lower : Array.Small n M b.2.1
  upper : Array.Small n M b.2.2
 theorem Small.mono {n M N : ℕ} {b : Data} (h : Small n M b) (hm : M≤N) : Small n N b := ⟨h.width.trans hm,h.lower.mono hm,h.upper.mono hm⟩
 theorem Small.midpoint {n M : ℕ} {b : Data} (h : Small n M b) : Array.Small n M (midpoint b) := h.lower.average h.upper
 theorem Small.withFloor {n M : ℕ} {b : Data} (h : Small n M b) {xs : List W} (hx : Array.Small n M xs) : Small n M (withFloor (b,xs)) := ⟨h.width,hx,h.upper⟩
 theorem Small.withCeiling {n M : ℕ} {b : Data} (h : Small n M b) {xs : List W} (hx : Array.Small n M xs) : Small n M (withCeiling (b,xs)) := ⟨h.width,h.lower,hx⟩
 theorem Small.clip {n M : ℕ} {b : Data} (h : Small n M b) {xs : List W} (hx : Array.Small n M xs) : Array.Small n M (clip (b,xs)) := h.upper.min (h.lower.max hx)
 theorem Small.averageClipped {n M : ℕ} {b : Data} (h : Small n M b) {xs ys : List W} (hx : Array.Small n M xs) (hy : Array.Small n M ys) : Array.Small n M (averageClipped (b,xs,ys)) := h.clip (hx.average hy)
 theorem centered_small {n M : ℕ} {w : W} (hw : w.digits.length≤M) {xs : List W} (hx : Array.Small n M xs) : Small n (M+3) (centered (w,xs)) := by
  refine ⟨?_,?_,(Array.Small.translate hw hx).mono (by omega)⟩
  · change (Word.double w).digits.length≤_; rw [Word.double_length]; omega
  · apply Array.Small.translate
    · change (Word.neg w).digits.length≤M+2; rw [Word.neg_length]; omega
    · exact hx.mono (by omega)
 theorem Small.capLow {n M : ℕ} {b : Data} (h : Small n M b) {w : W} (hw : w.digits.length≤M) : Small n (M+1) (capLow (b,w)) :=
  ⟨hw.trans (by omega),h.lower.mono (by omega),(h.upper.mono (by omega)).min (Array.Small.translate hw h.lower)⟩
 theorem Small.capHigh {n M : ℕ} {b : Data} (h : Small n M b) {w : W} (hw : w.digits.length≤M) : Small n (M+3) (capHigh (b,w)) := by
  refine ⟨hw.trans (by omega),?_,h.upper.mono (by omega)⟩
  apply (h.lower.mono (by omega)).max
  apply Array.Small.translate
  · change (Word.neg w).digits.length≤M+2; rw [Word.neg_length]; omega
  · exact h.upper.mono (by omega)
end RawBox
end MeanPayoff.TreeDevice.Certified

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Array
 theorem choose_bound {as bs : List W} {M : ℕ} (ha : Bounded as M) (hb : Bounded bs M) (hs : List Bool) :
    Bounded (choose (hs,as,bs)) M := by
  induction hs generalizing as bs with
  | nil => exact Bounded.nil _
  | cons c cs ih =>
    cases as with
    | nil =>
      change Bounded ((if c then zero else zero)::choose (cs,[],bs)) M
      exact Bounded.cons (by cases c <;> exact Nat.zero_le _) (ih (Bounded.nil _) hb)
    | cons a as =>
      cases bs with
      | nil =>
        apply Bounded.cons
        · change (if c then a else zero).digits.length≤M
          cases c
          · exact Nat.zero_le _
          · exact ha a (by simp)
        · exact ih (fun w hw => ha w (by simp [hw])) (Bounded.nil _)
      | cons b bs =>
        apply Bounded.cons
        · change (if c then a else b).digits.length≤M
          cases c
          · exact hb b (by simp)
          · exact ha a (by simp)
        · exact ih (fun w hw => ha w (by simp [hw])) (fun w hw => hb w (by simp [hw]))
 theorem choose_small {as bs : List W} {n M : ℕ} (ha : Small n M as) (hb : Small n M bs) (hs : List Bool) (hl : hs.length≤n) :
    Small n M (choose (hs,as,bs)) :=
  ⟨(zip_length _ _ hs _).le.trans hl,choose_bound ha.digits hb.digits hs⟩
end Array

namespace DetMass
structure Small (n M : ℕ) (r : Data) : Prop where
  den : r.1.digits.length≤M
  nums : Array.Small n M r.2

theorem Small.mono {n M N : ℕ} {r : Data} (h : Small n M r) (hm : M≤N) : Small n N r :=
  ⟨h.den.trans hm,h.nums.mono hm⟩

theorem short (r : ℤ) (hr : r=3 ∨ r=4 ∨ r=5 ∨ r=8 ∨ r=1536 ∨ r=2560) :
    (EdgeRead.encodedWord r).digits.length≤16 := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [RawBudget.encodedWord_length_nonneg _ (by norm_num)] <;> decide

theorem times_bound {M : ℕ} {w : W} (h : w.digits.length≤M) (r : ℤ)
    (hr : r=3 ∨ r=4 ∨ r=5 ∨ r=8 ∨ r=1536 ∨ r=2560) :
    (RawBudget.times r w).digits.length≤M+38 := by
  have ht := RawBudget.times_length r w
  have hs := short r hr
  omega

theorem scale_small {n M : ℕ} {r : Data} (h : Small n M r) : Small n (M+38) (scale 4 3 r) := by
  refine ⟨times_bound h.den 3 (by tauto),?_,?_⟩
  · change (r.2.map _).length≤n
    simpa only [List.length_map] using h.nums.length
  · intro w hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact times_bound (h.nums.digits v hv) 4 (by tauto)

theorem reweight_small {n M : ℕ} {r : Data} (h : Small n M r) (ls : List Bool) :
    Small n (M+38) (reweight (r,ls)) := by
  refine ⟨times_bound h.den 5 (by tauto),?_,?_⟩
  · exact (Array.zip_length _ false r.2 ls).le.trans h.nums.length
  · change Array.Bounded (Zip.zip _ false r.2 ls) (M+38)
    have go : ∀ (ws : List W) (bs : List Bool), Array.Bounded ws M →
        Array.Bounded (Zip.zip (Code.branch snd (fst.comp (RawBudget.times 4)) (fst.comp (RawBudget.times 8))).eval false ws bs) (M+38) := by
      intro ws
      induction ws with
      | nil => intro bs _; exact Array.Bounded.nil _
      | cons w ws ih =>
        intro bs hw
        cases bs with
        | nil =>
          exact Array.Bounded.cons (times_bound (hw w (by simp)) 8 (by tauto))
            (ih [] (fun v hv => hw v (by simp [hv])))
        | cons b bs =>
          apply Array.Bounded.cons
          · change (if b then RawBudget.times 4 w else RawBudget.times 8 w).digits.length≤M+38
            split
            · exact times_bound (hw w (by simp)) 4 (by tauto)
            · exact times_bound (hw w (by simp)) 8 (by tauto)
          · exact ih bs (fun v hv => hw v (by simp [hv]))
    exact go r.2 ls h.nums.digits
end DetMass

namespace DetRaw
structure Small (n M : ℕ) (x : Input) : Prop where
  width : x.1.1.digits.length≤M
  lower : Array.Small n M x.1.2
  a : DetMass.Small n M x.2.1
  b : DetMass.Small n M x.2.2

theorem Small.mono {n M N : ℕ} {x : Input} (h : Small n M x) (hm : M≤N) : Small n N x :=
  ⟨h.width.trans hm,h.lower.mono hm,h.a.mono hm,h.b.mono hm⟩

theorem piece_bound {n M : ℕ} {x : Input} (h : Small n M x) (k : ℕ) :
    (piece k x).digits.length≤M := (Word.shiftRight_length _ _).trans h.width

theorem amount_bound {n M : ℕ} {x : Input} (h : Small n M x) (r : ℤ) (hr : r=1536 ∨ r=2560) :
    (amount r x).digits.length≤M+38 := DetMass.times_bound (piece_bound h 12) r (by tauto)

theorem center_small {n M : ℕ} {x : Input} (h : Small n M x) : Array.Small n (M+1) (center x) :=
  Array.Small.translate (piece_bound h 1) h.lower

theorem child_small {n M : ℕ} {x : Input} {vs : List W}
    (h : Small n M x) (hv : Array.Small n M vs) (u : Bool) : Small n (M+40) (child u (x,vs)) := by
  have hl : Array.Small n (M+3) (Array.translate (Word.neg (piece 8 x),vs)) := by
    apply Array.Small.translate (M:=M+2)
    · rw [Word.neg_length]; have := piece_bound h 8; omega
    · exact hv.mono (by omega)
  cases u
  · exact ⟨(piece_bound h 7).trans (by omega),hl.mono (by omega),h.a.mono (by omega),
      (DetMass.scale_small h.b).mono (by omega)⟩
  · exact ⟨(piece_bound h 7).trans (by omega),hl.mono (by omega),
      (DetMass.scale_small h.a).mono (by omega),h.b.mono (by omega)⟩

theorem provisional_small {n M : ℕ} {x : Input} {vs : List W}
    (h : Small n M x) (hv : Array.Small n M vs) : Small n (M+40) (provisional (x,vs)) := by
  refine ⟨(piece_bound h 1).trans (by omega),?_,h.a.mono (by omega),h.b.mono (by omega)⟩
  apply Array.Small.mono (M:=M+3) _ (by omega)
  apply Array.Small.translate (M:=M+2)
  · change (Word.neg (piece 2 x)).digits.length≤M+2
    rw [Word.neg_length]; have := piece_bound h 2; omega
  · exact hv.mono (by omega)

theorem continuation_small {n M : ℕ} {x : Input} (h : Small n M x) (ls : List Bool) :
    Small n (M+40) (continuation (x,ls)) :=
  ⟨h.width.trans (by omega),h.lower.mono (by omega),
    (DetMass.reweight_small h.a ls).mono (by omega),
    (DetMass.reweight_small h.b (Array.complement ls)).mono (by omega)⟩

theorem minus_small {n M : ℕ} {x : Input} {vs : List W}
    (h : Small n M x) (hv : Array.Small n M vs) : Array.Small n (M+40) (minus (x,vs)) := by
  apply Array.Small.max
  · apply Array.Small.mono (M:=M+3) _ (by omega)
    apply Array.Small.translate (M:=M+2)
    · change (Word.neg (piece 12 x)).digits.length≤M+2
      rw [Word.neg_length]; have := piece_bound h 12; omega
    · exact hv.mono (by omega)
  · apply Array.Small.mono (M:=M+39) _ (by omega)
    exact Array.Small.translate (amount_bound h 1536 (by tauto)) (h.lower.mono (by omega))

theorem plus_small {n M : ℕ} {x : Input} {vs : List W}
    (h : Small n M x) (hv : Array.Small n M vs) : Array.Small n (M+40) (plus (x,vs)) := by
  apply Array.Small.min
  · exact (Array.Small.translate (piece_bound h 12) hv).mono (by omega)
  · apply Array.Small.mono (M:=M+39) _ (by omega)
    exact Array.Small.translate (amount_bound h 2560 (by tauto)) (h.lower.mono (by omega))

theorem down_small {n M : ℕ} {x : Input} {vs : List W}
    (h : Small n M x) (hv : Array.Small n M vs) (ls : List Bool) (hl : ls.length≤n) :
    Array.Small n (M+40) (down (x,vs,ls)) :=
  Array.choose_small (hv.mono (by omega)) (minus_small h hv) ls hl

theorem up_small {n M : ℕ} {x : Input} {vs : List W}
    (h : Small n M x) (hv : Array.Small n M vs) (ls : List Bool) (hl : ls.length≤n) :
    Array.Small n (M+40) (up (x,vs,ls)) :=
  Array.choose_small (plus_small h hv) (hv.mono (by omega)) ls hl

theorem baseLabels_length {n M : ℕ} {x : Input} (h : Small n M x) : (baseLabels x).length≤n :=
  (List.length_map _).le.trans h.b.nums.length

theorem basic_length {n M : ℕ} {x : Input} (h : Small n M x) (ar : RawBasic.Arena) :
    (basic (ar,x)).length≤n := by
  change (Zip.zip Word.lt.eval _ (Array.translate (x.1.1,x.1.2.map _)) _).length≤n
  rw [Array.zip_length]
  change (List.map _ (List.map _ x.1.2)).length≤n
  simpa only [List.length_map] using h.lower.length

theorem finish_length {n M : ℕ} {x : Input} {ds : List W} (hd : Array.Small n M ds)
    (us : List W) (ls : List Bool) : (finish (x,ds,us,ls)).length≤n := by
  change (Zip.zip _ _ (lowMark (x,ds)) _).length≤n
  rw [Array.zip_length]
  change (Zip.zip _ _ ds _).length≤n
  rw [Array.zip_length]
  exact hd.length
end DetRaw
end MeanPayoff.TreeDevice.Certified

end OAI
