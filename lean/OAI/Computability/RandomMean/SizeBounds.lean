import OAI.Computability.RandomMean.DispatchBounds

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Size
variable {α β : Type} [Encoding α] [Encoding β]
 theorem randomBool (b : Bool) : treeSize (encode b)≤7 := by cases b <;> decide
 theorem mask (bs : List Bool) : treeSize (encode bs)≤8*bs.length+1 := by
  have h := list_bound (xs:=bs) (M:=7) (fun b _ => randomBool b)
  omega
 theorem digits {w : W} {N : ℕ} (h : treeSize (encode w)≤N) : w.digits.length≤N := (digits_le_wordSize w).trans h
end Size
namespace Array
 theorem randomSmallOfSize {xs : List W} {N : ℕ} (h : treeSize (encode xs)≤N) : Small N N xs :=
  ⟨(Size.length xs).trans h,(bounded_size xs).mono h⟩
 theorem Small.randomSize {xs : List W} {n M : ℕ} (h : Small n M xs) : treeSize (encode xs)≤n*(4*M+6)+1 :=
  (size_bound h.digits).trans (by gcongr; exact h.length)
end Array
namespace RawBudget
 theorem small_of_size {p : Data} {N : ℕ} (h : treeSize (encode p)≤N) : Small N N p := by
  have h1 := (Size.fst p).trans h
  have h2 := (Size.snd p).trans h
  have h21 := (Size.fst p.2).trans h2
  have h22 := (Size.snd p.2).trans h2
  exact ⟨Size.digits ((Size.fst p.1).trans h1),Size.digits ((Size.snd p.1).trans h1),
    Size.digits ((Size.fst p.2.1).trans h21),Size.digits ((Size.snd p.2.1).trans h21),
    Array.randomSmallOfSize ((Size.fst p.2.2).trans h22),Array.randomSmallOfSize ((Size.snd p.2.2).trans h22)⟩
end RawBudget
namespace RawBox
 theorem small_of_size {b : Data} {N : ℕ} (h : treeSize (encode b)≤N) : Small N N b := by
  have h2 := (Size.snd b).trans h
  exact ⟨Size.digits ((Size.fst b).trans h),Array.randomSmallOfSize ((Size.fst b.2).trans h2),
    Array.randomSmallOfSize ((Size.snd b.2).trans h2)⟩
end RawBox
namespace RawOrientation
 theorem small_of_size {o : Data} {N : ℕ} (h : treeSize (encode o)≤N) : Small N o := by
  intro bs hb
  exact (Size.length bs).trans ((Size.mem hb).trans ((Size.snd o).trans h))
 theorem listMass_size (os : List Data) : listMass os≤treeSize (encode os) := by
  induction os with
  | nil => exact Nat.zero_le _
  | cons o os ih =>
    rw [listMass_cons]
    have ho := (Size.length o.2).trans (Size.snd o)
    change _≤treeSize (listTree encode (o::os))
    rw [listTree,treeSize_pair]
    change _≤treeSize (listTree encode os) at ih
    omega
 theorem small_size {o : Data} {n : ℕ} (h : Small n o) :
    treeSize (encode o)≤o.2.length*(8*n+2)+9 := by
  have hl := Size.list_bound (xs:=o.2) (M:=8*n+1) (fun b hb => (Size.mask b).trans (by gcongr; exact h b hb))
  have hb := Size.randomBool o.1
  rw [←Prod.eta o,Size.pair]
  dsimp only
  nlinarith
 theorem many_size {os : List Data} {n : ℕ} (h : ∀ o∈os, Small n o) :
    treeSize (encode os)≤listMass os*(8*n+2)+10*os.length+1 := by
  induction os with
  | nil => change treeSize Data.nil≤_; simp only [treeSize_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,RawOrientation.listMass_nil]; omega
  | cons o os ih =>
    have ho := small_size (h o (by simp))
    have ht := ih (fun q hq => h q (by simp [hq]))
    change treeSize (listTree encode (o::os))≤_
    rw [listTree,treeSize_pair,listMass_cons,List.length_cons]
    change treeSize (listTree encode os)≤_ at ht
    nlinarith
end RawOrientation
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
 theorem Pack.fields_size (z : Pack) :
    treeSize (encode z.p)≤treeSize (encode z) ∧
    treeSize (encode z.b)≤treeSize (encode z) ∧
    treeSize (encode z.t)≤treeSize (encode z) ∧
    treeSize (encode z.q)≤treeSize (encode z) ∧
    treeSize (encode z.r)≤treeSize (encode z) ∧
    treeSize (encode z.vs)≤treeSize (encode z) ∧
    treeSize (encode z.o)≤treeSize (encode z) ∧
    treeSize (encode z.os)≤treeSize (encode z) := by
  have h1 := Size.fst z.tuple
  have h2 := Size.snd z.tuple
  have h3 := (Size.snd z.tuple.2).trans h2
  have h4 := (Size.snd z.tuple.2.2).trans h3
  have h5 := (Size.snd z.tuple.2.2.2).trans h4
  have h6 := (Size.snd z.tuple.2.2.2.2).trans h5
  have h7 := (Size.snd z.tuple.2.2.2.2.2).trans h6
  exact ⟨h1,(Size.fst z.tuple.2).trans h2,(Size.fst z.tuple.2.2).trans h3,
    (Size.fst z.tuple.2.2.2).trans h4,(Size.fst z.tuple.2.2.2.2).trans h5,
    (Size.fst z.tuple.2.2.2.2.2).trans h6,(Size.fst z.tuple.2.2.2.2.2.2).trans h7,
    (Size.snd z.tuple.2.2.2.2.2.2).trans h7⟩
 theorem Pack.small_of_size {z : Pack} {N : ℕ} (h : treeSize (encode z)≤N) : z.Small N N N := by
  rcases z.fields_size with ⟨hp,hb,ht,hq,hr,hvs,ho,hos⟩
  exact ⟨RawBudget.small_of_size (hp.trans h),RawBox.small_of_size (hb.trans h),
    (Size.length z.t).trans (ht.trans h),Array.randomSmallOfSize (hq.trans h),Array.randomSmallOfSize (hr.trans h),
    fun xs hx => Array.randomSmallOfSize ((Size.mem hx).trans (hvs.trans h)),
    RawOrientation.small_of_size (ho.trans h),
    fun o ho' => RawOrientation.small_of_size ((Size.mem ho').trans (hos.trans h))⟩
 theorem Pack.mass_size (z : Pack) : z.mass≤4*treeSize (encode z) := by
  rcases z.fields_size with ⟨_,_,_,_,_,hvs,ho,hos⟩
  have h1 := (Size.length z.vs).trans hvs
  have h2 := (Size.length z.o.2).trans ((Size.snd z.o).trans ho)
  have h3 := (Size.length z.os).trans hos
  have h4 := (RawOrientation.listMass_size z.os).trans hos
  dsimp only [Pack.mass]; omega
 theorem Pack.small_size {z : Pack} {n H M U : ℕ} (h : z.Small n H M)
    (hu : 1≤U) (hn : n≤U) (hh : H≤U) (hm : M≤U) (hz : z.mass≤U) :
    treeSize (encode z)≤1024*U^3 := by
  have u2 : U≤U^2 := Nat.le_pow (by decide : 0<2)
  have u3 : U^2≤U^3 := Nat.pow_le_pow_right hu (by omega)
  have a (xs : List W) (ha : Array.Small n M xs) : treeSize (encode xs)≤12*U^2 := by
    have ht := ha.randomSize
    have hab : n*(4*M+6)≤U*(4*U+6) := Nat.mul_le_mul hn (by omega)
    nlinarith
  have w (v : W) (hv : v.digits.length≤M) : treeSize (encode v)≤10*U := by
    have hw := wordSize_bound v
    change treeSize (encode v)≤4*v.digits.length+5 at hw
    omega
  have hp : treeSize (encode z.p)≤72*U^2 := by
    have h1 := w _ h.p.kn
    have h2 := w _ h.p.kd
    have h3 := w _ h.p.mn
    have h4 := w _ h.p.md
    have h5 := a _ h.p.alpha
    have h6 := a _ h.p.beta
    rw [←Prod.eta z.p,Size.pair,←Prod.eta z.p.1,Size.pair,
      ←Prod.eta z.p.2,Size.pair,←Prod.eta z.p.2.1,Size.pair,←Prod.eta z.p.2.2,Size.pair]
    nlinarith
  have hb : treeSize (encode z.b)≤40*U^2 := by
    have h1 := w _ h.b.width
    have h2 := a _ h.b.lower
    have h3 := a _ h.b.upper
    rw [←Prod.eta z.b,Size.pair,←Prod.eta z.b.2,Size.pair]
    nlinarith
  have ht : treeSize (encode z.t)≤3*U := by rw [Size.count]; have := h.t; omega
  have hq := a _ h.q
  have hr := a _ h.r
  have hvlen : z.vs.length≤U := by dsimp only [Pack.mass] at hz; omega
  have hoLen : z.o.2.length≤U := by dsimp only [Pack.mass] at hz; omega
  have hosLen : z.os.length≤U := by dsimp only [Pack.mass] at hz; omega
  have hosMass : RawOrientation.listMass z.os≤U := by dsimp only [Pack.mass] at hz; omega
  have hv : treeSize (encode z.vs)≤14*U^3 := by
    have ht := Size.list_bound (fun xs hx => a xs (h.vs xs hx))
    have hb := Nat.mul_le_mul_right (12*U^2+1) hvlen
    nlinarith
  have ho : treeSize (encode z.o)≤20*U^2 := by
    have ht := RawOrientation.small_size h.o
    have hb := Nat.mul_le_mul hoLen (show 8*n+2≤8*U+2 by omega)
    nlinarith
  have hos : treeSize (encode z.os)≤22*U^2 := by
    have ht := RawOrientation.many_size h.os
    have hb := Nat.mul_le_mul hosMass (show 8*n+2≤8*U+2 by omega)
    nlinarith
  change treeSize (encode z.tuple)≤_
  simp only [Pack.tuple,Size.pair]
  nlinarith
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
 def StackTags (H : ℕ) (ks : List Cell) : Prop := ∀ c∈ks, c.1.length≤H
 def StateTags (H : ℕ) (s : State) : Prop := s.1.1.length≤H ∧ StackTags H s.2
 @[simp] theorem stackTags_nil (H : ℕ) : StackTags H [] := by intro c hc; cases hc
 @[simp] theorem stackTags_cons (H : ℕ) (c : Cell) (ks : List Cell) : StackTags H (c::ks) ↔ c.1.length≤H ∧ StackTags H ks := by simp [StackTags]
 theorem StackTags.tail {H : ℕ} {ks : List Cell} (h : StackTags H ks) : StackTags H ks.tail := fun c hc => h c (List.mem_of_mem_tail hc)
 theorem JobLabel.tags (j : JobLabel) {H : ℕ} {x : Input} (hH : 22≤H) (hk : StackTags H (stack x)) : StateTags H (j.code x) := by
  cases j <;>
    simp only [JobLabel.code,solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,
      orientPlusCase,tightenCase,reweightCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [StateTags,ret,call,save,push,makeCell,pair_eval,comp_eval,const_eval,
      cons_eval,List.length_replicate,stackTags_cons,hk,and_true] <;> omega
 theorem FrameLabel.tags (j : FrameLabel) {H : ℕ} {x : Input} (hH : 22≤H) (hk : StackTags H (rest x)) : StateTags H (j.code x) := by
  cases j <;>
    simp only [FrameLabel.code,trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,
      centersHeadCase,orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,
      tightenFirstCase,tightenSecondCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,
      solveReweightedCase,capHighCase,capLowCase,includeInnerCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [StateTags,ret,call,push,makeCell,pair_eval,comp_eval,const_eval,
      cons_eval,List.length_replicate,stackTags_cons,hk,and_true] <;> omega
 theorem dispatch_tags {H : ℕ} {x : Input} (hH : 22≤H) (h : StateTags H (state x)) : StateTags H (dispatch x) := by
  apply Code.select_spec
  · exact jobs_spec x _ (fun j => j.tags hH h.2)
  · simp only [resume,branch_eval]
    split
    · exact h
    · apply Code.select_spec
      · exact frames_spec x _ (fun j => j.tags hH h.2.tail)
      · exact h
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Size
@[simp] theorem cons {α : Type} [Encoding α] (a : α) (as : List α) :
    treeSize (encode (a::as))=treeSize (encode a)+treeSize (encode as)+1 := treeSize_pair _ _
end Size
namespace RawControl
 theorem stackMass_mem {ks : List Cell} {c : Cell} (hc : c∈ks) : c.2.mass≤ stackMass ks := by
  induction ks with
  | nil => cases hc
  | cons d ds ih =>
    rw [stackMass_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    · have := ih hc; omega
 theorem stackMass_size (ks : List Cell) : stackMass ks≤4*treeSize (encode ks) := by
  induction ks with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    rw [stackMass_cons,Size.cons]
    have hp := c.2.mass_size
    have hc := Size.snd c
    omega
 theorem stateMass_size (s : State) : stateMass s≤4*treeSize (encode s) := by
  have h1 := s.1.2.mass_size
  have h2 := stackMass_size s.2
  have h3 := Size.snd s.1
  rw [←Prod.eta s,Size.pair]
  dsimp only [stateMass]; omega
 theorem stateSmall_of_size {s : State} {N : ℕ} (h : treeSize (encode s)≤N) : StateSmall N N N s := by
  exact ⟨Pack.small_of_size ((Size.snd s.1).trans ((Size.fst s).trans h)),
    fun c hc => Pack.small_of_size ((Size.snd c).trans ((Size.mem hc).trans ((Size.snd s).trans h)))⟩
 theorem stateTags_of_size {s : State} {N : ℕ} (h : treeSize (encode s)≤N) : StateTags N s := by
  exact ⟨(Size.length s.1.1).trans ((Size.fst s.1).trans ((Size.fst s).trans h)),
    fun c hc => (Size.length c.1).trans ((Size.fst c).trans ((Size.mem hc).trans ((Size.snd s).trans h)))⟩
 theorem StateTags.mono {s : State} {H N : ℕ} (h : StateTags H s) (hm : H≤N) : StateTags N s :=
  ⟨h.1.trans hm,fun c hc => (h.2 c hc).trans hm⟩
 theorem state_small_size {s : State} {n H M U : ℕ} (h : StateSmall n H M s)
    (ht : StateTags U s) (hu : 1≤U) (hn : n≤U) (hh : H≤U) (hm : M≤U)
    (hs : stateMass s≤U) (hk : s.2.length≤U) : treeSize (encode s)≤4096*U^4 := by
  have u2 : U≤U^2 := Nat.le_pow (by decide)
  have u3 : U^2≤U^3 := Nat.pow_le_pow_right hu (by omega)
  have u4 : U^3≤U^4 := Nat.pow_le_pow_right hu (by omega)
  have cell (c : Cell) (hp : c.2.Small n H M) (htag : c.1.length≤U) (hmass : c.2.mass≤U) :
      treeSize (encode c)≤1028*U^3 := by
    have hpk := Pack.small_size hp hu hn hh hm hmass
    rw [←Prod.eta c,Size.pair,Size.count]
    nlinarith
  have hhead : treeSize (encode s.1)≤1028*U^3 := cell s.1 h.1 ht.1 (by dsimp only [stateMass] at hs; omega)
  have htail : treeSize (encode s.2)≤1030*U^4 := by
    have ht' := Size.list_bound (xs:=s.2) (M:=1028*U^3) (fun c hc => cell c (h.2 c hc) (ht.2 c hc) (by
      have := stackMass_mem hc; dsimp only [stateMass] at hs; omega))
    have hmul := Nat.mul_le_mul_right (1028*U^3+1) hk
    nlinarith
  rw [←Prod.eta s,Size.pair]
  nlinarith
end RawControl
end MeanPayoff.TreeDevice.Certified

end

end OAI
