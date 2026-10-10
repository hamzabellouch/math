import OAI.Computability.RandomMean.Growth

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
structure Pack.Small (n H M : ℕ) (z : Pack) : Prop where
  p : RawBudget.Small n M z.p
  b : RawBox.Small n M z.b
  t : z.t.length≤H
  q : Array.Small n M z.q
  r : Array.Small n M z.r
  vs : ∀ xs∈z.vs, Array.Small n M xs
  o : RawOrientation.Small n z.o
  os : ∀ v∈z.os, RawOrientation.Small n v
 theorem Pack.Small.mono {n H M N : ℕ} {z : Pack} (h : z.Small n H M) (hm : M≤N) : z.Small n H N :=
  ⟨h.p.mono hm,h.b.mono hm,h.t,h.q.mono hm,h.r.mono hm,fun xs hx => (h.vs xs hx).mono hm,h.o,h.os⟩
 theorem zeroBudget_small (n M : ℕ) : RawBudget.Small n M zeroBudget :=
  ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _⟩
 theorem zeroBox_small (n M : ℕ) : RawBox.Small n M zeroBox := ⟨Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _⟩
 theorem zeroOrient_small (n : ℕ) : RawOrientation.Small n (false,[]) := by intro bs hb; cases hb
 theorem Pack.zero_small (n H M : ℕ) : Pack.zero.Small n H M :=
  ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,by simp [Pack.zero],zeroOrient_small _,by simp [Pack.zero]⟩
 def StackSmall (n H M : ℕ) (ks : List Cell) : Prop := ∀ c∈ks, c.2.Small n H M
 def StateSmall (n H M : ℕ) (s : State) : Prop := s.1.2.Small n H M ∧ StackSmall n H M s.2
 theorem StackSmall.mono {n H M N : ℕ} {ks : List Cell} (h : StackSmall n H M ks) (hm : M≤N) : StackSmall n H N ks := fun c hc => (h c hc).mono hm
 theorem StackSmall.tail {n H M : ℕ} {ks : List Cell} (h : StackSmall n H M ks) : StackSmall n H M ks.tail := fun c hc => h c (List.mem_of_mem_tail hc)
 theorem StackSmall.head {n H M : ℕ} {ks : List Cell} (h : StackSmall n H M ks) : (ks.headD ([],Pack.zero)).2.Small n H M := by
  cases ks with
  | nil => exact Pack.zero_small _ _ _
  | cons c cs => exact h c (by simp)
 theorem StackSmall.cons {n H M : ℕ} {ks : List Cell} {c : Cell} (hc : c.2.Small n H M) (h : StackSmall n H M ks) : StackSmall n H M (c::ks) := by
  intro d hd; rcases List.mem_cons.mp hd with rfl | hd
  · exact hc
  · exact h d hd
 theorem StateSmall.mono {n H M N : ℕ} {s : State} (h : StateSmall n H M s) (hm : M≤N) : StateSmall n H N s := ⟨h.1.mono hm,h.2.mono hm⟩
 theorem narrow_small {n M : ℕ} {x : Input} (bc : Code Input RawBox.Data) (vc : Code Input (List W))
    (hb : RawBox.Small n M (bc x)) (hv : Array.Small n M (vc x)) : RawBox.Small n (M+3) (narrow bc vc x) := by
  apply RawBox.centered_small _ hv
  exact (Word.shiftRight_length _ _).trans hb.width
 theorem wide_small {n M : ℕ} {x : Input} (bc : Code Input RawBox.Data) (vc : Code Input (List W))
    (hb : RawBox.Small n M (bc x)) (hv : Array.Small n M (vc x)) : RawBox.Small n (M+3) (wide bc vc x) := by
  apply RawBox.centered_small _ hv
  exact (Word.shiftRight_length _ _).trans hb.width
 theorem capWidth_small {n M : ℕ} {x : Input} (bc : Code Input RawBox.Data) (hb : RawBox.Small n M (bc x)) :
    (capWidth bc x).digits.length≤M+3 := by
  change (Word.sub ((bc x).1,delta bc x)).digits.length≤_
  rw [Word.sub_length]
  have hd : (delta bc x).digits.length≤M := (Word.shiftRight_length _ _).trans hb.width
  have := hb.width
  omega
 theorem centerAt_small {n M : ℕ} {x : Input} (ic : Code Input Count)
    (hb : RawBox.Small n M ((caller ≫ₚ b) x)) (hv : ∀ xs∈(current x).vs, Array.Small n M xs) :
    Array.Small n M (centerAt ic x) := by
  simp only [centerAt,comp_eval,pair_eval,vs_eval,getD_eval]
  exact Array.Small.getD hv _ hb.midpoint
 theorem lastPositive_small {n M : ℕ} {x : Input}
    (hb : RawBox.Small n M ((caller ≫ₚ b) x)) (hv : ∀ xs∈(current x).vs, Array.Small n M xs) :
    (lastPositive x).length≤n := by
  change (RawOrientation.positives (_,_,centerAt _ x)).length≤n
  rw [RawOrientation.positives_length]
  exact (centerAt_small _ hb hv).length
 theorem lastNegative_small {n M : ℕ} {x : Input}
    (hb : RawBox.Small n M ((caller ≫ₚ b) x)) (hv : ∀ xs∈(current x).vs, Array.Small n M xs) :
    (lastNegative x).length≤n := by
  change (RawOrientation.negatives (_,_,centerAt _ x)).length≤n
  rw [RawOrientation.negatives_length]
  exact (centerAt_small _ hb hv).length
 theorem basic_small {n M E : ℕ} {x : Input} (bc : Code Input RawBox.Data)
    (hb : RawBox.Small n M (bc x)) (he : RawBasic.ArenaBounded x.1.1 E) :
    Array.Small n (M+x.1.2.2.2.2.length*(E+1)) (basic bc x) := RawBasic.solve_small he hb _
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
 theorem job_small {G : Game} {B : ℕ} {A : SourceControl.Result G B}
    (j : SourceControl.Job G B A) {n H M E D : ℕ} {x : Input}
    (hc : (current x).Small n H M) (hk : StackSmall n H M (stack x))
    (hs : x.1.2.2.1.length≤H) (hj : x.1.2.2.2.1.length≤H)
    (he : RawBasic.ArenaBounded x.1.1 E) (hd : x.1.2.2.2.2.length*(E+1)+20≤D) :
    StateSmall n H (M+D) (jobCode j x) := by
  have hmd : M≤M+D := by omega
  have hd3 : M+3≤M+D := by omega
  have hd14 : M+14≤M+D := by omega
  have hdB : M+x.1.2.2.2.2.length*(E+1)≤M+D := by omega
  have hc' := hc.mono hmd
  have hk' := hk.mono hmd
  cases j with
  | solve P I =>
    simp only [jobCode,solveCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,RawBox.Small.smallVector hc'.b hc'.p,
        Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · split
      · refine ⟨?_,hk'⟩
        exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,(basic_small _ hc.b he).mono hdB,
          Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · refine ⟨?_,StackSmall.cons hc' hk'⟩
        exact ⟨hc'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | ask P I =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc'.p,hc'.b,hj,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | trials P I t =>
    simp only [jobCode,trialsCase,branch_eval]
    split
    · exact ⟨Pack.zero_small _ _ _,hk'⟩
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | update P hR I hB v =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc.p.reduceK.mono hd14,(narrow_small _ _ hc.b hc.q).mono hd3,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centers P hR I hB t v =>
    simp only [jobCode,centersCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,?_,zeroOrient_small _,(by intro v hv; cases hv)⟩
      intro xs hx
      change xs∈[(current x).q] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact hc'.q
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orient P hR I =>
    simp only [jobCode,orientCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.base_small _ _ ((basic_small _ hc.b he).mono hdB),(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons hc' hk'⟩
      exact ⟨hc'.p,hc'.b,hs,hc'.b.midpoint,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientTrials P hR I t =>
    simp only [jobCode,orientTrialsCase,branch_eval]
    split
    · exact ⟨Pack.zero_small _ _ _,hk'⟩
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientPlus P hR I =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc'.p,hc'.b,hj,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | tighten P hR I hB =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc.p.reduceK.mono hd14,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | reweight P hR I side hs =>
    simp only [jobCode,reweightCase,branch_eval]
    split
    · exact ⟨Pack.zero_small _ _ _,hk'⟩
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · refine ⟨?_,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
        simp only [call,makeCell,pair_eval,pack_eval,branch_eval]
        split
        · exact (hc.p.reweightM _).mono hd14
        · exact (hc.p.reweightK _).mono hd14
      · refine ⟨hc'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),?_,(by intro v hv; cases hv)⟩
        intro xs hx
        exact hc.o xs (List.mem_of_mem_tail hx)
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
 theorem mask_head {n : ℕ} {bs : List (List Bool)} (h : ∀ b∈bs, b.length≤n) : (bs.headD []).length≤n := by
  cases bs with
  | nil => exact Nat.zero_le _
  | cons b bs => exact h b (by simp)
 theorem frame_small {G : Game} {B : ℕ} {A C : SourceControl.Result G B}
    (f : SourceControl.Frame G B A C) {n H M D : ℕ} {x : Input}
    (hc : (current x).Small n H M) (hf : (caller x).Small n H M) (hk : StackSmall n H M (rest x))
    (hd : 20≤D) : StateSmall n H (M+D) (frameCode f x) := by
  have hmd : M≤M+D := by omega
  have hd3 : M+3≤M+D := by omega
  have hd6 : M+3+3≤M+D := by omega
  have hd14 : M+14≤M+D := by omega
  have hc' := hc.mono hmd
  have hf' := hf.mono hmd
  have hk' := hk.mono hmd
  cases f with
  | trialsHead P I t =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | vectorCons v =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,?_,zeroOrient_small _,(by intro v hv; cases hv)⟩
    intro xs hx
    change xs∈(caller x).q::(current x).vs at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hf'.q
    · exact hc'.vs xs hx
  | median I =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,RawMedian.boxed_small hf'.b hc'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centerFirst P hR I hB v =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf.p.reduceM.mono hd14,(narrow_small _ _ hf.b hf.q).mono hd3,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,hc'.q,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centerSecond I hB v r =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hf'.b.averageClipped hf'.r hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centersHead P hR I hB t v =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hf'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientLoop P hR I hB =>
    have hp := lastPositive_small hf.b hc.vs
    have hn := lastNegative_small hf.b hc.vs
    simp only [frameCode,orientLoopCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.trueComplement_small hp,(by intro v hv; cases hv)⟩
    · split
      · refine ⟨?_,hk'⟩
        exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.falseComplement_small hn,(by intro v hv; cases hv)⟩
      · refine ⟨?_,StackSmall.cons ?_ hk'⟩
        · exact ⟨hf'.p,(wide_small _ _ hf.b (centerAt_small _ hf.b hc.vs)).mono hd3,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
        · refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),?_,(by intro v hv; cases hv)⟩
          intro bs hbs
          change bs∈[lastPositive x,lastNegative x] at hbs
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hbs
          rcases hbs with rfl | rfl <;> assumption
  | orientTail H N =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),?_,(by intro v hv; cases hv)⟩
    exact RawOrientation.extend_small hc.o (mask_head hf.o) (mask_head (fun bs hbs => hf.o bs (List.mem_of_mem_tail hbs)))
  | orientHead P hR I t =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hc.o,(by intro v hv; cases hv)⟩
  | orientCons O =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,?_⟩
    intro v hv
    change v∈(caller x).o::(current x).os at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hf.o
    · exact hc.os v hv
  | combine P =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.combine_small hc.os,(by intro v hv; cases hv)⟩
  | tightenFirst P hR I hB =>
    simp only [frameCode,tightenFirstCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,hf'.b.withFloor hc'.q,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons hf' hk'⟩
      exact ⟨hf.p.reduceM.mono hd14,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | tightenSecond P hR I hB =>
    simp only [frameCode,tightenSecondCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,hf'.b.withCeiling hc'.q,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | floor I v | ceiling I v =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveTight P hR I hB =>
    refine ⟨?_,StackSmall.cons ?_ (StackSmall.cons (Pack.zero_small _ _ _) hk')⟩
    · exact ⟨hf'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨hf'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveOriented P hR I hB =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hc.o,(by intro v hv; cases hv)⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),(by intro v hv; cases hv),(by intro v hv; cases hv)⟩
  | reweightHead P hR I side hs =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hf.o,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveReweighted P hR I hB side =>
    have hw := capWidth_small (x:=x) (caller ≫ₚ b) hf.b
    simp only [frameCode,solveReweightedCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,((hf.b.mono (by omega : M≤M+3)).capHigh hw).mono hd6,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,hc'.vs,zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,((hf.b.mono (by omega : M≤M+3)).capLow hw).mono (by omega),Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,hc'.vs,zeroOrient_small _,(by intro v hv; cases hv)⟩
  | capHigh I hB vs =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q.foldMin hf'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | capLow I hB vs =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q.foldMax hf'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | includeInner I =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace RawOrientation
 def listMass (os : List Data) : ℕ := (os.map (fun o => o.2.length)).sum
 @[simp] theorem listMass_nil : listMass []=0 := rfl
 @[simp] theorem listMass_cons (o : Data) (os : List Data) : listMass (o::os)=o.2.length+listMass os := rfl
 theorem base_length (p : RawBudget.Data) (b : RawBox.Data) (xs : List W) : (base (p,b,xs)).2.length=1 := by
  change (if RawBudget.measureLarge (p,baseMask (b,xs)) then trueComplement (baseMask (b,xs)) else singleton (false,baseMask (b,xs))).2.length=1
  split <;> rfl
 theorem combine_length (os : List Data) : (combine os).2.length=listMass os := by
  change (Code.flatten (os.map Prod.snd)).length=_
  simp only [listMass,Code.flatten_eval,List.length_flatten,List.map_map,Function.comp_def]
 theorem extend_length (o : Data) (hs ns : List Bool) : (extend (o,hs,ns)).2.length=o.2.length+2 := by
  change (Code.append (o.2,[hs,ns])).length=_
  simp only [Code.append_eval,List.length_append,List.length_cons,List.length_nil]
end RawOrientation
namespace RawControl
 def Pack.mass (z : Pack) : ℕ := z.vs.length+z.o.2.length+z.os.length+RawOrientation.listMass z.os
 def stackMass (ks : List Cell) : ℕ := (ks.map (fun c => c.2.mass)).sum
 def stateMass (s : State) : ℕ := s.1.2.mass+stackMass s.2
 @[simp] theorem stackMass_nil : stackMass []=0 := rfl
 @[simp] theorem stackMass_cons (c : Cell) (ks : List Cell) : stackMass (c::ks)=c.2.mass+stackMass ks := rfl
 theorem job_mass {G : Game} {B : ℕ} {A : SourceControl.Result G B} (j : SourceControl.Job G B A) (x : Input) :
    stateMass (jobCode j x)≤ stateMass (state x)+3 ∧ (jobCode j x).2.length≤(stack x).length+2 := by
  cases j <;>
    simp only [jobCode,solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,
      orientPlusCase,tightenCase,reweightCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [stateMass,ret,call,save,push,makeCell,pair_eval,comp_eval,pack_eval,const_eval,
      cons_eval,tail_eval,stackMass_cons,Pack.mass,p_eval,b_eval,t_eval,q_eval,o_eval,      List.length_nil,List.length_cons,RawOrientation.listMass_nil,      RawOrientation.base_length,List.length_tail] <;>
    dsimp only [state,stack,current,Code.comp_eval,Code.fst_eval,Code.snd_eval] <;> omega
 theorem frame_mass {G : Game} {B : ℕ} {A C : SourceControl.Result G B} (f : SourceControl.Frame G B A C) (x : Input) :
    stateMass (frameCode f x)≤(current x).mass+(caller x).mass+stackMass (rest x)+3 ∧
      (frameCode f x).2.length≤(rest x).length+2 := by
  cases f <;>
    simp only [frameCode,trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,
      centersHeadCase,orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,
      tightenFirstCase,tightenSecondCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,
      solveReweightedCase,capHighCase,capLowCase,includeInnerCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [stateMass,ret,call,push,makeCell,pair_eval,comp_eval,pack_eval,const_eval,
      cons_eval,tail_eval,stackMass_cons,Pack.mass,p_eval,b_eval,t_eval,q_eval,r_eval,vs_eval,o_eval,os_eval,
      List.length_nil,List.length_cons,RawOrientation.listMass_nil,RawOrientation.listMass_cons,
      RawOrientation.extend_length,RawOrientation.combine_length,      RawOrientation.trueComplement,RawOrientation.falseComplement,RawOrientation.singleton,Pack.zero] <;>
    simp only [Code.comp_eval,Code.fst_eval,Code.snd_eval,      current,caller,stack,rest,state,Code.head_eval,Code.tail_eval] <;> omega
end RawControl
end MeanPayoff.TreeDevice.Certified

end

end OAI
