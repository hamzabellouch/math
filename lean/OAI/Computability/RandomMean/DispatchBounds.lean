import OAI.Computability.RandomMean.StateGrowth

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
inductive JobLabel where
  | solve | ask | trials | update | centers | orient | orientTrials | orientPlus | tighten | reweight
noncomputable def JobLabel.code : JobLabel → Code Input State
  | .solve => solveCase
  | .ask => askCase
  | .trials => trialsCase
  | .update => updateCase
  | .centers => centersCase
  | .orient => orientCase
  | .orientTrials => orientTrialsCase
  | .orientPlus => orientPlusCase
  | .tighten => tightenCase
  | .reweight => reweightCase
inductive FrameLabel where
  | trialsHead | vectorCons | median | centerFirst | centerSecond | centersHead | orientLoop | orientTail | orientHead | orientCons | combine | tightenFirst | tightenSecond | floor | ceiling | solveTight | solveOriented | reweightHead | solveReweighted | capHigh | capLow | includeInner
noncomputable def FrameLabel.code : FrameLabel → Code Input State
  | .trialsHead => trialsHeadCase
  | .vectorCons => vectorConsCase
  | .median => medianCase
  | .centerFirst => centerFirstCase
  | .centerSecond => centerSecondCase
  | .centersHead => centersHeadCase
  | .orientLoop => orientLoopCase
  | .orientTail => orientTailCase
  | .orientHead => orientHeadCase
  | .orientCons => orientConsCase
  | .combine => combineCase
  | .tightenFirst => tightenFirstCase
  | .tightenSecond => tightenSecondCase
  | .floor => boxPassCase
  | .ceiling => boxPassCase
  | .solveTight => solveTightCase
  | .solveOriented => solveOrientedCase
  | .reweightHead => reweightHeadCase
  | .solveReweighted => solveReweightedCase
  | .capHigh => capHighCase
  | .capLow => capLowCase
  | .includeInner => includeInnerCase
 theorem JobLabel.small (j : JobLabel) {n H M E D : ℕ} {x : Input}
    (hc : (current x).Small n H M) (hk : StackSmall n H M (stack x))
    (hs : x.1.2.2.1.length≤H) (hj : x.1.2.2.2.1.length≤H)
    (he : RawBasic.ArenaBounded x.1.1 E) (hd : x.1.2.2.2.2.length*(E+1)+20≤D) :
    StateSmall n H (M+D) (JobLabel.code j x) := by
  have hmd : M≤M+D := by omega
  have hd3 : M+3≤M+D := by omega
  have hd14 : M+14≤M+D := by omega
  have hdB : M+x.1.2.2.2.2.length*(E+1)≤M+D := by omega
  have hc' := hc.mono hmd
  have hk' := hk.mono hmd
  cases j with
  | solve =>
    simp only [JobLabel.code,solveCase,branch_eval]
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
  | ask =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc'.p,hc'.b,hj,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | trials =>
    simp only [JobLabel.code,trialsCase,branch_eval]
    split
    · exact ⟨Pack.zero_small _ _ _,hk'⟩
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | update =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc.p.reduceK.mono hd14,(narrow_small _ _ hc.b hc.q).mono hd3,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centers =>
    simp only [JobLabel.code,centersCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,?_,zeroOrient_small _,(by intro v hv; cases hv)⟩
      intro xs hx
      change xs∈[(current x).q] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact hc'.q
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orient =>
    simp only [JobLabel.code,orientCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.base_small _ _ ((basic_small _ hc.b he).mono hdB),(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons hc' hk'⟩
      exact ⟨hc'.p,hc'.b,hs,hc'.b.midpoint,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientTrials =>
    simp only [JobLabel.code,orientTrialsCase,branch_eval]
    split
    · exact ⟨Pack.zero_small _ _ _,hk'⟩
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientPlus =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc'.p,hc'.b,hj,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | tighten =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc.p.reduceK.mono hd14,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | reweight =>
    simp only [JobLabel.code,reweightCase,branch_eval]
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
 theorem FrameLabel.small (f : FrameLabel) {n H M D : ℕ} {x : Input}
    (hc : (current x).Small n H M) (hf : (caller x).Small n H M) (hk : StackSmall n H M (rest x))
    (hd : 20≤D) : StateSmall n H (M+D) (FrameLabel.code f x) := by
  have hmd : M≤M+D := by omega
  have hd3 : M+3≤M+D := by omega
  have hd6 : M+3+3≤M+D := by omega
  have hd14 : M+14≤M+D := by omega
  have hc' := hc.mono hmd
  have hf' := hf.mono hmd
  have hk' := hk.mono hmd
  cases f with
  | trialsHead =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | vectorCons =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,?_,zeroOrient_small _,(by intro v hv; cases hv)⟩
    intro xs hx
    change xs∈(caller x).q::(current x).vs at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hf'.q
    · exact hc'.vs xs hx
  | median =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,RawMedian.boxed_small hf'.b hc'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centerFirst =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf.p.reduceM.mono hd14,(narrow_small _ _ hf.b hf.q).mono hd3,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,hc'.q,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centerSecond =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hf'.b.averageClipped hf'.r hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centersHead =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hf'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientLoop =>
    have hp := lastPositive_small hf.b hc.vs
    have hn := lastNegative_small hf.b hc.vs
    simp only [FrameLabel.code,orientLoopCase,branch_eval]
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
  | orientTail =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),?_,(by intro v hv; cases hv)⟩
    exact RawOrientation.extend_small hc.o (mask_head hf.o) (mask_head (fun bs hbs => hf.o bs (List.mem_of_mem_tail hbs)))
  | orientHead =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hc.o,(by intro v hv; cases hv)⟩
  | orientCons =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,?_⟩
    intro v hv
    change v∈(caller x).o::(current x).os at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hf.o
    · exact hc.os v hv
  | combine =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.combine_small hc.os,(by intro v hv; cases hv)⟩
  | tightenFirst =>
    simp only [FrameLabel.code,tightenFirstCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,hf'.b.withFloor hc'.q,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons hf' hk'⟩
      exact ⟨hf.p.reduceM.mono hd14,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | tightenSecond =>
    simp only [FrameLabel.code,tightenSecondCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,hf'.b.withCeiling hc'.q,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | floor | ceiling =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveTight =>
    refine ⟨?_,StackSmall.cons ?_ (StackSmall.cons (Pack.zero_small _ _ _) hk')⟩
    · exact ⟨hf'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨hf'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveOriented =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hc.o,(by intro v hv; cases hv)⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),(by intro v hv; cases hv),(by intro v hv; cases hv)⟩
  | reweightHead =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hf.o,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveReweighted =>
    have hw := capWidth_small (x:=x) (caller ≫ₚ b) hf.b
    simp only [FrameLabel.code,solveReweightedCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,((hf.b.mono (by omega : M≤M+3)).capHigh hw).mono hd6,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,hc'.vs,zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,((hf.b.mono (by omega : M≤M+3)).capLow hw).mono (by omega),Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,hc'.vs,zeroOrient_small _,(by intro v hv; cases hv)⟩
  | capHigh =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q.foldMin hf'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | capLow =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q.foldMax hf'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | includeInner =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
 theorem JobLabel.mass (j : JobLabel) (x : Input) :
    stateMass (JobLabel.code j x)≤ stateMass (state x)+3 ∧ (JobLabel.code j x).2.length≤(stack x).length+2 := by
  cases j <;>
    simp only [JobLabel.code,solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,
      orientPlusCase,tightenCase,reweightCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [stateMass,ret,call,save,push,makeCell,pair_eval,comp_eval,pack_eval,const_eval,
      cons_eval,tail_eval,stackMass_cons,Pack.mass,p_eval,b_eval,t_eval,q_eval,o_eval,      List.length_nil,List.length_cons,RawOrientation.listMass_nil,      RawOrientation.base_length,List.length_tail] <;>
    dsimp only [state,stack,current,Code.comp_eval,Code.fst_eval,Code.snd_eval] <;> omega
 theorem FrameLabel.mass (f : FrameLabel) (x : Input) :
    stateMass (FrameLabel.code f x)≤(current x).mass+(caller x).mass+stackMass (rest x)+3 ∧
      (FrameLabel.code f x).2.length≤(rest x).length+2 := by
  cases f <;>
    simp only [FrameLabel.code,trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,
      centersHeadCase,orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,
      tightenFirstCase,tightenSecondCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,
      solveReweightedCase,capHighCase,capLowCase,includeInnerCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [stateMass,ret,call,push,makeCell,pair_eval,comp_eval,pack_eval,const_eval,
      cons_eval,tail_eval,stackMass_cons,Pack.mass,p_eval,b_eval,t_eval,q_eval,r_eval,vs_eval,o_eval,os_eval,
      List.length_nil,List.length_cons,RawOrientation.listMass_nil,RawOrientation.listMass_cons,
      RawOrientation.extend_length,RawOrientation.combine_length,      RawOrientation.trueComplement,RawOrientation.falseComplement,RawOrientation.singleton,Pack.zero] <;>
    simp only [Code.comp_eval,Code.fst_eval,Code.snd_eval,      current,caller,stack,rest,state,Code.head_eval,Code.tail_eval] <;> omega
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Code
 theorem select_spec {α β : Type} [Encoding α] [Encoding β] (tag : Code α Count) (cases : List (Code α β))
    (fallback : Code α β) (x : α) (P : β→Prop) (hc : ∀ c∈cases, P (c x)) (hf : P (fallback x)) :
    P (select tag cases fallback x) := by
  induction cases generalizing tag with
  | nil => exact hf
  | cons c cs ih =>
    simp only [select,branch_eval]
    split
    · exact hc c (by simp)
    · exact ih _ (fun d hd => hc d (by simp [hd]))
end Code
namespace RawControl
 theorem jobs_spec (x : Input) (P : State→Prop) (h : ∀ j : JobLabel, P (j.code x)) :
    ∀ c ∈ [solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,orientPlusCase,tightenCase,reweightCase], P (c x) := by
  intro c hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h .solve
  · exact h .ask
  · exact h .trials
  · exact h .update
  · exact h .centers
  · exact h .orient
  · exact h .orientTrials
  · exact h .orientPlus
  · exact h .tighten
  · exact h .reweight
 theorem frames_spec (x : Input) (P : State→Prop) (h : ∀ j : FrameLabel, P (j.code x)) :
    ∀ c ∈ [trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,centersHeadCase,orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,tightenFirstCase,tightenSecondCase,boxPassCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,solveReweightedCase,capHighCase,capLowCase,includeInnerCase], P (c x) := by
  intro c hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h .trialsHead
  · exact h .vectorCons
  · exact h .median
  · exact h .centerFirst
  · exact h .centerSecond
  · exact h .centersHead
  · exact h .orientLoop
  · exact h .orientTail
  · exact h .orientHead
  · exact h .orientCons
  · exact h .combine
  · exact h .tightenFirst
  · exact h .tightenSecond
  · exact h .floor
  · exact h .ceiling
  · exact h .solveTight
  · exact h .solveOriented
  · exact h .reweightHead
  · exact h .solveReweighted
  · exact h .capHigh
  · exact h .capLow
  · exact h .includeInner
 theorem caller_mass (x : Input) : (caller x).mass+stackMass (rest x)=stackMass (stack x) := by
  change ((stack x).headD ([],Pack.zero)).2.mass+stackMass (stack x).tail=stackMass (stack x)
  cases stack x <;> rfl
 theorem dispatch_small {n H M E D : ℕ} {x : Input}
    (hc : (current x).Small n H M) (hk : StackSmall n H M (stack x))
    (hs : x.1.2.2.1.length≤H) (hj : x.1.2.2.2.1.length≤H)
    (he : RawBasic.ArenaBounded x.1.1 E) (hd : x.1.2.2.2.2.length*(E+1)+20≤D) :
    StateSmall n H (M+D) (dispatch x) := by
  have hmd : M≤M+D := by omega
  have h0 : StateSmall n H (M+D) (state x) := ⟨hc.mono hmd,hk.mono hmd⟩
  apply Code.select_spec
  · exact jobs_spec x _ (fun j => j.small hc hk hs hj he hd)
  · simp only [resume,branch_eval]
    split
    · exact h0
    · apply Code.select_spec
      · exact frames_spec x _ (fun f => f.small hc hk.head hk.tail (by omega))
      · exact h0
 theorem dispatch_mass (x : Input) :
    stateMass (dispatch x)≤ stateMass (state x)+3 ∧ (dispatch x).2.length≤(stack x).length+2 := by
  have h0 : stateMass (state x)≤ stateMass (state x)+3 ∧ (state x).2.length≤(stack x).length+2 := by
    constructor <;> exact Nat.le_add_right _ _
  refine Code.select_spec _ _ _ x (fun z => stateMass z ≤ stateMass (state x)+3 ∧ z.2.length≤(stack x).length+2) ?_ ?_
  · exact jobs_spec x (fun z => stateMass z ≤ stateMass (state x)+3 ∧ z.2.length≤(stack x).length+2) (fun j => j.mass x)
  · simp only [resume,branch_eval]
    split
    · exact h0
    · refine Code.select_spec _ _ _ x (fun z => stateMass z ≤ stateMass (state x)+3 ∧ z.2.length≤(stack x).length+2) ?_ ?_
      · apply frames_spec x (fun z => stateMass z ≤ stateMass (state x)+3 ∧ z.2.length≤(stack x).length+2)
        intro f
        have h := f.mass x
        have hm := caller_mass x
        have ht : (rest x).length≤(stack x).length := by
          change (stack x).tail.length≤(stack x).length
          rw [List.length_tail]; omega
        change _≤(current x).mass+stackMass (stack x)+3 ∧ _≤_ at ⊢
        omega
      · exact h0
end RawControl
end MeanPayoff.TreeDevice.Certified

end

end OAI
