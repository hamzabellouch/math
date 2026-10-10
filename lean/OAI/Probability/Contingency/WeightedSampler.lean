import Mathlib
import OAI.Probability.Contingency.AllMarginLaw

namespace OAI

/-! Weighted Sampler. -/

noncomputable section


namespace Contingency.BitModel.StackCode.WeightedSampler
noncomputable section

def preg (i : Fin PreparedIntegerCall.program.work) : Fin 8 := ⟨i.val,by have := i.isLt; change i.val<6 at this; omega⟩
abbrev first : Program := ⟨PreparedIntegerCall.program.labels,8,PreparedIntegerCall.program.start,
  fun q => Registers.op preg (PreparedIntegerCall.program.code q)⟩
def sreg : Fin 4→Fin 8 := ![5,4,6,7]
abbrev second : Program := ⟨WeightedScan.program.labels,8,WeightedScan.program.start,
  fun q => Registers.op sreg (WeightedScan.program.code q)⟩
def program : Program := Sequence.program first second.labels second.start second.code

theorem preg_injective : Function.Injective preg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)
theorem sreg_injective : Function.Injective sreg := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem reverse_value (xs : List Bool) : BinarySubtract.value xs.reverse=BinaryTrial.beValue xs := by
  refine List.reverseRecOn xs rfl ?_
  intro xs b ih
  simp only [List.reverse_append,List.reverse_singleton,List.singleton_append,BinarySubtract.value,
    IntegerDraw.beValue_snoc,ih]
  omega

theorem first_safe (N : ℕ) (rest a : List Bool)
    (h : (a.foldl (fun c b => step first b c) (initial first (encodeNat N++rest))).state=none) :
    ∃ u : Fin (N+1),
      (a.foldl (fun c b => step first b c) (initial first (encodeNat N++rest))).memory.stack 5=
        (IntegerDraw.integerWord N u).reverse ∧
      (a.foldl (fun c b => step first b c) (initial first (encodeNat N++rest))).memory.stack 6=[] ∧
      (a.foldl (fun c b => step first b c) (initial first (encodeNat N++rest))).memory.stack 7=[] ∧
      (a.foldl (fun c b => step first b c) (initial first (encodeNat N++rest))).memory.input=rest ∧
      (a.foldl (fun c b => step first b c) (initial first (encodeNat N++rest))).memory.outputRev=[] := by
  have hr := Registers.fold_rel PreparedIntegerCall.program preg preg_injective a
    (show Registers.ConfigRel PreparedIntegerCall.program preg
      (initial PreparedIntegerCall.program (encodeNat N++rest)) (initial first (encodeNat N++rest)) from
      ⟨rfl,(fun _ => rfl),rfl,rfl,rfl⟩)
  obtain ⟨u,hu,hi,ho⟩ := PreparedIntegerCall.finite_memory_safe N rest a (hr.1.symm.trans h)
  refine ⟨u,(hr.2.1 PreparedIntegerCall.outputRegister).trans hu,?_,?_,hr.2.2.1.trans hi,hr.2.2.2.1.trans ho⟩
  · exact Registers.fold_frame PreparedIntegerCall.program preg a (initial first (encodeNat N++rest)) 6
      (by intro i he; have hh := congrArg Fin.val he; have := i.isLt; change i.val<6 at this; simp [preg] at hh; omega)
  · exact Registers.fold_frame PreparedIntegerCall.program preg a (initial first (encodeNat N++rest)) 7
      (by intro i he; have hh := congrArg Fin.val he; have := i.isLt; change i.val<6 at this; simp [preg] at hh; omega)

def project (m : Memory 8) : Memory 4 :=
  ⟨m.input,m.consumed,fun i => m.stack (sreg i),fun i => m.blanks (sreg i),m.outputRev⟩

 

theorem select_run (N : ℕ) (ws : List (List Bool)) (u : Fin (N+1)) (m : Memory 8) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size) (htotal : WeightedScan.weightTotal ws=N+1)
    (ha : m.stack 5=(IntegerDraw.integerWord N u).reverse)
    (h6 : m.stack 6=[]) (h7 : m.stack 7=[])
    (hi : m.input=ws.flatten++rest) (ho : m.outputRev=[]) :
    ∃ t j : ℕ,t*2≤10*(N.size+1)*ws.length ∧ j<ws.length ∧
      Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j ∧
      ∀ b : List Bool,b.length=t →
        (b.foldl (fun c x => step second x c) ⟨some second.start,m⟩).state=none ∧
        (b.foldl (fun c x => step second x c) ⟨some second.start,m⟩).memory.outputRev=List.replicate j false := by
  let as := (IntegerDraw.integerWord N u).reverse
  have hv : BinarySubtract.value as=u.val := by simp [as,reverse_value]
  have hl : as.length=N.size := by simp [as]
  obtain ⟨j,m',hj,hs,hex,heout⟩ := WeightedScan.scan_run ws as (project m) rest 0
    (fun w hw => (hlen w hw).trans hl.symm) ha hi h6 h7
    (by rw [hv,htotal]; exact u.isLt)
  let t := 3*as.length+2*0+3+j*(5*as.length+5)
  refine ⟨t,j,?_,hj,?_,?_⟩
  · have hm := Nat.mul_le_mul_left (5*as.length+5) (Nat.succ_le_iff.mpr hj)
    dsimp only [t]
    rw [← hl]
    nlinarith only [hm]
  · simpa only [hv,Nat.zero_add] using hs
  · intro b hb
    have hcfg : Registers.ConfigRel WeightedScan.program sreg
        (WeightedScan.config (.start false) (project m)) (⟨some second.start,m⟩ : Config second) :=
      ⟨rfl,(fun _ => rfl),rfl,rfl,rfl⟩
    have hr := Registers.fold_rel WeightedScan.program sreg sreg_injective b hcfg
    have he : b.foldl (fun c x => step WeightedScan.program x c)
        (WeightedScan.config (.start false) (project m))=⟨none,m'⟩ := by
      rw [WeightedScan.fold_independent b (List.replicate t false) (by simpa using hb)]
      exact hex
    rw [he] at hr
    refine ⟨hr.1,?_⟩
    exact hr.2.2.2.1.trans (by simpa [project,ho] using heout)

end
end Contingency.BitModel.StackCode.WeightedSampler

 

 

 

namespace Contingency.BitModel.StackCode.WeightedSampler
noncomputable section

 

theorem after_first (N : ℕ) (ws : List (List Bool)) (rest a : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size) (htotal : WeightedScan.weightTotal ws=N+1)
    (hfirst : Sequence.FirstHalt first (initial first (encodeNat N++(ws.flatten++rest))) a) :
    ∃ (t j : ℕ) (u : Fin (N+1)),t≤5*(N.size+1)*ws.length ∧ j<ws.length ∧
      Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j ∧
      (a.foldl (fun c x => step first x c) (initial first (encodeNat N++(ws.flatten++rest)))).memory.stack 5=
        (IntegerDraw.integerWord N u).reverse ∧
      ∀ b : List Bool,b.length=t →
        ((a++b).foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))).state=none ∧
        ((a++b).foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))).memory.outputRev=
          List.replicate j false := by
  have hh := Sequence.firstHalt_result first _ a hfirst
  obtain ⟨u,hu,h6,h7,hi,ho⟩ := first_safe N (ws.flatten++rest) a hh
  obtain ⟨t,j,ht,hj,hs,hr⟩ := select_run N ws u _ rest hlen htotal hu h6 h7 hi ho
  refine ⟨t,j,u,by nlinarith only [ht],hj,hs,hu,?_⟩
  intro b hb
  have he := Sequence.link_run first second.labels second.start second.code
    (initial first (encodeNat N++(ws.flatten++rest))) a b hfirst
  change (a++b).foldl (fun c x => step program x c)
    (initial program (encodeNat N++(ws.flatten++rest)))=_ at he
  rw [he]
  obtain ⟨hs,ho⟩ := hr b hb
  constructor
  · change Option.map (Fin.natAdd first.labels) _=none
    have hs' : (b.foldl (fun c v =>
        step (Sequence.rightProgram first second.labels second.start second.code) v c)
        ⟨some second.start,(a.foldl (fun c v => step first v c)
          (initial first (encodeNat N++(ws.flatten++rest)))).memory⟩).state=none := hs
    rw [hs']
    rfl
  · exact ho

 

theorem finishes_after (N : ℕ) (ws : List (List Bool)) (rest xs : List Bool) (s : ℕ)
    (hlen : ∀ w∈ws,w.length=N.size) (htotal : WeightedScan.weightTotal ws=N+1)
    (hl : s+5*(N.size+1)*ws.length≤xs.length)
    (hh : ((xs.take s).foldl (fun c x => step first x c)
      (initial first (encodeNat N++(ws.flatten++rest)))).state=none) :
    (xs.foldl (fun c x => step program x c)
      (initial program (encodeNat N++(ws.flatten++rest)))).state=none := by
  obtain ⟨a,z,haz,hfirst,he⟩ := Sequence.first_prefix first _ (xs.take s) hh
  obtain ⟨t,j,u,ht,hj,hscan,hu,hr⟩ := after_first N ws rest a hlen htotal hfirst
  have ha : a.length ≤ s := by
    have h₁ := congrArg List.length haz
    have h₂ := List.length_take_le s xs
    simp only [List.length_append] at h₁
    omega
  have hpre : xs.take a.length=a := by
    have h₁ := congrArg (List.take a.length) haz
    simpa [List.take_take,Nat.min_eq_left ha] using h₁
  let b := (xs.drop a.length).take t
  let c := (xs.drop a.length).drop t
  have hb : b.length=t := by
    simp only [b,List.length_take,List.length_drop]
    exact Nat.min_eq_left (by omega)
  have hdecomp : xs=(a++b)++c := by
    rw [List.append_assoc]
    change xs=a++((xs.drop a.length).take t++(xs.drop a.length).drop t)
    rw [List.take_append_drop]
    exact (List.take_append_drop a.length xs).symm.trans (congrArg (fun z => z++xs.drop a.length) hpre)
  obtain ⟨hd,ho⟩ := hr b hb
  rw [hdecomp,List.foldl_append]
  rw [Sequence.halted_fold program _ hd c]
  exact hd

end
end Contingency.BitModel.StackCode.WeightedSampler

 

 

 

namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
open WeightedSampler
noncomputable section

abbrev draw : Program := WeightedSampler.first
abbrev selector : Program := WeightedSampler.second

theorem padded_select (N : ℕ) (ws : List (List Bool)) (u : Fin (N+1)) (m : Memory 8) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1)
    (ha : m.stack 5=(IntegerDraw.integerWord N u).reverse++[false])
    (h6 : m.stack 6=[]) (h7 : m.stack 7=[])
    (hi : m.input=ws.flatten++rest) (ho : m.outputRev=[]) :
    ∃ t j : ℕ,t*2≤10*(N.size+2)*ws.length ∧ j<ws.length ∧
      Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j ∧
      ∀ b : List Bool,b.length=t →
        (b.foldl (fun c x => step selector x c) ⟨some selector.start,m⟩).state=none ∧
        (b.foldl (fun c x => step selector x c) ⟨some selector.start,m⟩).memory.outputRev=List.replicate j false := by
  let as := (IntegerDraw.integerWord N u).reverse++[false]
  have hv : BinarySubtract.value as=u.val := by
    simpa only [as,← List.replicate_one] using (BinarySubtract.value_append_false (IntegerDraw.integerWord N u).reverse 1).trans (by simp [WeightedSampler.reverse_value])
  have hl : as.length=N.size+1 := by simp [as]
  obtain ⟨j,m',hj,hs,hex,heout⟩ := WeightedScan.scan_run ws as (project m) rest 0
    (fun w hw => (hlen w hw).trans hl.symm) ha hi h6 h7
    (by rw [hv,htotal]; exact u.isLt)
  let t := 3*as.length+2*0+3+j*(5*as.length+5)
  refine ⟨t,j,?_,hj,?_,?_⟩
  · have hm := Nat.mul_le_mul_left (5*as.length+5) (Nat.succ_le_iff.mpr hj)
    dsimp only [t]
    have he : N.size+2=as.length+1 := by omega
    rw [he]
    nlinarith only [hm]
  · simpa only [hv,Nat.zero_add] using hs
  · intro b hb
    have hcfg : Registers.ConfigRel WeightedScan.program sreg
        (WeightedScan.config (.start false) (project m)) (⟨some selector.start,m⟩ : Config selector) :=
      ⟨rfl,(fun _ => rfl),rfl,rfl,rfl⟩
    have hr := Registers.fold_rel WeightedScan.program sreg sreg_injective b hcfg
    have he : b.foldl (fun c x => step WeightedScan.program x c)
        (WeightedScan.config (.start false) (project m))=⟨none,m'⟩ := by
      rw [WeightedScan.fold_independent b (List.replicate t false) (by simpa using hb)]
      exact hex
    rw [he] at hr
    refine ⟨hr.1,?_⟩
    exact hr.2.2.2.1.trans (by simpa [project,ho] using heout)

abbrev post : Program := Sequence.program HighPad.program selector.labels selector.start selector.code
def program : Program := Sequence.program draw post.labels post.start post.code

theorem post_run (N : ℕ) (ws : List (List Bool)) (u : Fin (N+1)) (m : Memory 8) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1)
    (ha : m.stack 5=(IntegerDraw.integerWord N u).reverse)
    (h6 : m.stack 6=[]) (h7 : m.stack 7=[])
    (hi : m.input=ws.flatten++rest) (ho : m.outputRev=[]) :
    ∃ t j : ℕ,t≤4*N.size+8+5*(N.size+2)*ws.length ∧ j<ws.length ∧
      Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j ∧
      ∀ b : List Bool,b.length=t →
        (b.foldl (fun c x => step post x c) ⟨some post.start,m⟩).state=none ∧
        (b.foldl (fun c x => step post x c) ⟨some post.start,m⟩).memory.outputRev=List.replicate j false := by
  obtain ⟨T,m',hT,h5',h6',hframe,hi',ho',hr⟩ := HighPad.pad (IntegerDraw.integerWord N u).reverse m ha h6
  have hpad := hr (List.replicate T false) (by simp)
  obtain ⟨k,hk,hfirst⟩ := Sequence.deterministic_first_time HighPad.program
    (noCoin_deterministic _ HighPad.noCoin) ⟨some HighPad.program.start,m⟩ T
    (by rw [hpad])
  obtain ⟨s,j,hs,hj,hscan,hsel⟩ := padded_select N ws u m' rest hlen htotal h5' h6'
    ((hframe 7 (by decide) (by decide)).trans h7) (hi'.trans hi) (ho'.trans ho)
  refine ⟨k+s,j,?_,hj,hscan,?_⟩
  · simp only [List.length_reverse,IntegerDraw.integerWord_length] at hT
    nlinarith only [hk,hT,hs]
  · intro b hb
    let a := b.take k
    let c := b.drop k
    have ha' : a.length=k := by simp only [a,List.length_take,hb]; omega
    have hc : c.length=s := by simp [c,hb]
    have hf := hfirst a ha'
    have hf' := hf.2.trans hpad
    have he := Sequence.link_run HighPad.program selector.labels selector.start selector.code
      ⟨some HighPad.program.start,m⟩ a c hf.1
    rw [hf'] at he
    have hbc : a++c=b := List.take_append_drop k b
    rw [hbc] at he
    obtain ⟨hd,hout⟩ := hsel c hc
    have hresult : (c.foldl (fun cfg x => step (Sequence.rightProgram HighPad.program selector.labels selector.start selector.code) x cfg)
        ⟨some selector.start,m'⟩).state=none := hd
    change b.foldl (fun cfg x => step post x cfg) ⟨some post.start,m⟩=_ at he
    rw [he]
    constructor
    · change Option.map (Fin.natAdd HighPad.program.labels) _=none
      rw [hresult]; rfl
    · exact hout

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

 

 

 

namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
open WeightedSampler
noncomputable section

 

theorem after_first (N : ℕ) (ws : List (List Bool)) (rest a : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1)
    (hfirst : Sequence.FirstHalt draw (initial draw (encodeNat N++(ws.flatten++rest))) a) :
    ∃ (t j : ℕ) (u : Fin (N+1)),t≤(4*N.size+8+5*(N.size+2)*ws.length) ∧ j<ws.length ∧
      Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j ∧
      (a.foldl (fun c x => step draw x c) (initial draw (encodeNat N++(ws.flatten++rest)))).memory.stack 5=
        (IntegerDraw.integerWord N u).reverse ∧
      ∀ b : List Bool,b.length=t →
        ((a++b).foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))).state=none ∧
        ((a++b).foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))).memory.outputRev=
          List.replicate j false := by
  have hh := Sequence.firstHalt_result draw _ a hfirst
  obtain ⟨u,hu,h6,h7,hi,ho⟩ := first_safe N (ws.flatten++rest) a hh
  obtain ⟨t,j,ht,hj,hs,hr⟩ := post_run N ws u _ rest hlen htotal hu h6 h7 hi ho
  refine ⟨t,j,u,ht,hj,hs,hu,?_⟩
  intro b hb
  have he := Sequence.link_run draw post.labels post.start post.code
    (initial draw (encodeNat N++(ws.flatten++rest))) a b hfirst
  change (a++b).foldl (fun c x => step program x c)
    (initial program (encodeNat N++(ws.flatten++rest)))=_ at he
  rw [he]
  obtain ⟨hs,ho⟩ := hr b hb
  constructor
  · change Option.map (Fin.natAdd draw.labels) _=none
    have hs' : (b.foldl (fun c v =>
        step (Sequence.rightProgram draw post.labels post.start post.code) v c)
        ⟨some post.start,(a.foldl (fun c v => step draw v c)
          (initial draw (encodeNat N++(ws.flatten++rest)))).memory⟩).state=none := hs
    rw [hs']
    rfl
  · exact ho

 

theorem finishes_after (N : ℕ) (ws : List (List Bool)) (rest xs : List Bool) (s : ℕ)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1)
    (hl : s+(4*N.size+8+5*(N.size+2)*ws.length)≤xs.length)
    (hh : ((xs.take s).foldl (fun c x => step draw x c)
      (initial draw (encodeNat N++(ws.flatten++rest)))).state=none) :
    (xs.foldl (fun c x => step program x c)
      (initial program (encodeNat N++(ws.flatten++rest)))).state=none := by
  obtain ⟨a,z,haz,hfirst,he⟩ := Sequence.first_prefix draw _ (xs.take s) hh
  obtain ⟨t,j,u,ht,hj,hscan,hu,hr⟩ := after_first N ws rest a hlen htotal hfirst
  have ha : a.length ≤ s := by
    have h₁ := congrArg List.length haz
    have h₂ := List.length_take_le s xs
    simp only [List.length_append] at h₁
    omega
  have hpre : xs.take a.length=a := by
    have h₁ := congrArg (List.take a.length) haz
    simpa [List.take_take,Nat.min_eq_left ha] using h₁
  let b := (xs.drop a.length).take t
  let c := (xs.drop a.length).drop t
  have hb : b.length=t := by
    simp only [b,List.length_take,List.length_drop]
    exact Nat.min_eq_left (by omega)
  have hdecomp : xs=(a++b)++c := by
    rw [List.append_assoc]
    change xs=a++((xs.drop a.length).take t++(xs.drop a.length).drop t)
    rw [List.take_append_drop]
    exact (List.take_append_drop a.length xs).symm.trans (congrArg (fun z => z++xs.drop a.length) hpre)
  obtain ⟨hd,ho⟩ := hr b hb
  rw [hdecomp,List.foldl_append]
  rw [Sequence.halted_fold program _ hd c]
  exact hd

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.WeightedSampler
noncomputable section

def storedMass (N : ℕ) (rest : List Bool) (u : Fin (N+1)) (s : ℕ) : ℝ :=
  ((Finset.univ.filter fun f : Fin s→Bool => (run first (encodeNat N++rest) f).state=none ∧
    (run first (encodeNat N++rest) f).memory.stack 5=(IntegerDraw.integerWord N u).reverse).card:ℝ)/2^s

theorem stored_refinement (N : ℕ) (rest : List Bool) :
    ∃ t≤9*N.size+6,∀ (s : ℕ) (f : Fin (t+s)→Bool),
      ((run first (encodeNat N++rest) f).state=none ↔
        (run IntegerDraw.program (IntegerDraw.rawMaximum N) (fun i => f (Fin.natAdd t i))).state=none) ∧
      (run first (encodeNat N++rest) f).memory.stack 5=
        (run IntegerDraw.program (IntegerDraw.rawMaximum N) (fun i => f (Fin.natAdd t i))).memory.outputRev := by
  obtain ⟨t,ht,hr⟩ := PreparedIntegerCall.refinement N rest
  refine ⟨t,ht,?_⟩
  intro s f
  let a := List.ofFn fun i : Fin t => f (i.castAdd s)
  let b := List.ofFn fun i : Fin s => f (Fin.natAdd t i)
  obtain ⟨c,hc,hm,hi,ho⟩ := hr a (by simp [a]) b
  have he : a++b=List.ofFn f := by
    dsimp only [a,b]
    rw [List.ofFn_add]
    congr 2
  rw [he] at hc
  have hg := Registers.fold_rel PreparedIntegerCall.program preg preg_injective (List.ofFn f)
    (show Registers.ConfigRel PreparedIntegerCall.program preg
      (initial PreparedIntegerCall.program (encodeNat N++rest)) (initial first (encodeNat N++rest)) from
      ⟨rfl,(fun _ => rfl),rfl,rfl,rfl⟩)
  rw [hc] at hg
  constructor
  · have hgs : (run first (encodeNat N++rest) f).state=Option.map (Fin.natAdd PrepareMaximum.program.labels) c.state := hg.1
    constructor
    · intro hh
      have hz : c.state=none := Option.map_eq_none_iff.mp (hgs.symm.trans hh)
      exact hm.1.symm.trans hz
    · intro hh
      have hz : c.state=none := hm.1.trans hh
      exact hgs.trans (Option.map_eq_none_iff.mpr hz)
  · exact (hg.2.1 PreparedIntegerCall.outputRegister).trans hm.2.2.2

theorem stored_shifted (N : ℕ) (rest : List Bool) :
    ∃ t≤9*N.size+6,∀ s : ℕ,
      (∀ u : Fin (N+1),storedMass N rest u (t+s)=
        mass IntegerDraw.program (IntegerDraw.rawMaximum N) (IntegerDraw.integerWord N u) s) ∧
      tail first (encodeNat N++rest) (t+s)=tail IntegerDraw.program (IntegerDraw.rawMaximum N) s := by
  classical
  obtain ⟨t,ht,hr⟩ := stored_refinement N rest
  have hi : ∀ s,Function.Injective (Fin.natAdd t : Fin s→Fin (t+s)) := by
    intro s i j h; simpa using h
  refine ⟨t,ht,?_⟩
  intro s
  constructor
  · intro u
    unfold storedMass mass
    have hre (x : List Bool) : (x=(IntegerDraw.integerWord N u).reverse) ↔ x.reverse=IntegerDraw.integerWord N u := by
      constructor
      · intro h; simp only [h,List.reverse_reverse]
      · intro h; simpa only [List.reverse_reverse] using congrArg List.reverse h
    simp only [(hr s _).1,(hr s _).2,hre]
    simpa only [Fintype.card_fin,Function.comp_def] using CoordinateLaw.probability_restrict (Fin.natAdd t) (hi s)
      (fun f => (run IntegerDraw.program (IntegerDraw.rawMaximum N) f).state=none ∧
        (run IntegerDraw.program (IntegerDraw.rawMaximum N) f).memory.outputRev.reverse=IntegerDraw.integerWord N u)
  · unfold tail
    simp only [ne_eq,(hr s _).1]
    simpa only [Fintype.card_fin,Function.comp_def] using CoordinateLaw.probability_restrict (Fin.natAdd t) (hi s)
      (fun f => (run IntegerDraw.program (IntegerDraw.rawMaximum N) f).state≠none)

theorem stored_summable (N : ℕ) (rest : List Bool) : Summable (tail first (encodeNat N++rest)) := by
  obtain ⟨t,ht,hl⟩ := stored_shifted N rest
  apply (summable_nat_add_iff t).1
  simpa only [Nat.add_comm,(hl _).2] using IntegerDraw.stack_summable (IntegerDraw.rawMaximum N)

theorem stored_uniform (N : ℕ) (rest : List Bool) (u : Fin (N+1)) :
    Tendsto (storedMass N rest u) atTop (nhds (1/(N+1:ℝ))) := by
  obtain ⟨t,ht,hl⟩ := stored_shifted N rest
  apply (tendsto_add_atTop_iff_nat t).1
  simpa only [Nat.add_comm,(hl _).1,IntegerDraw.rawMaximum_value,IntegerDraw.integerWord] using
    IntegerDraw.stack_uniform (IntegerDraw.rawMaximum N) ⟨u,by simpa using u.isLt⟩

theorem stored_expected (N : ℕ) (rest : List Bool) :
    (∑' s,tail first (encodeNat N++rest) s)≤35*(N.size:ℝ)+21 := by
  obtain ⟨t,ht,hl⟩ := stored_shifted N rest
  have hs := stored_summable N rest
  rw [← hs.sum_add_tsum_nat_add t]
  have hb : (∑ s∈Finset.range t,tail first (encodeNat N++rest) s)≤(t:ℝ) := by
    calc
      _ ≤ ∑ s∈Finset.range t,(1:ℝ) := by
        exact Finset.sum_le_sum fun _ _ => IntegerDraw.tail_le_one _ _ _
      _ = _ := by simp
  have he : (∑' s,tail first (encodeNat N++rest) (s+t))=
      ∑' s,tail IntegerDraw.program (IntegerDraw.rawMaximum N) s := by
    congr 1
    funext s
    simpa only [Nat.add_comm] using (hl s).2
  rw [he]
  have hw : 2^(IntegerDraw.rawMaximum N).length≤
      2*(BinaryTrial.beValue (IntegerDraw.rawMaximum N)+1) := by
    simpa using IntegerDraw.minimal_width N
  have hi := IntegerDraw.stack_linear_expected (IntegerDraw.rawMaximum N) hw
  simp only [IntegerDraw.rawMaximum_length] at hi
  have ht' : (t:ℝ)≤9*(N.size:ℝ)+6 := by exact_mod_cast ht
  push_cast at hi
  linarith

end
end Contingency.BitModel.StackCode.WeightedSampler

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
noncomputable section

def delay (N : ℕ) (ws : List (List Bool)) : ℕ := 4*N.size+8+5*(N.size+2)*ws.length

theorem tail_delay (N : ℕ) (ws : List (List Bool)) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1) (s : ℕ) :
    tail program (encodeNat N++(ws.flatten++rest)) (s+delay N ws) ≤
      tail draw (encodeNat N++(ws.flatten++rest)) s := by
  classical
  let e : Fin s→Fin (s+delay N ws) := Fin.castAdd (delay N ws)
  have hi : Function.Injective e := by
    intro i j h; exact Fin.ext (congrArg (fun k : Fin (s+delay N ws) => k.val) h)
  let p : (Fin s→Bool)→Prop := fun f => (run draw (encodeNat N++(ws.flatten++rest)) f).state≠none
  have he := CoordinateLaw.probability_restrict e hi p
  simp only [Fintype.card_fin] at he
  unfold tail
  change _≤((Finset.univ.filter p).card:ℝ)/2^s
  rw [← he]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show
    (Finset.univ.filter fun f : Fin (s+delay N ws)→Bool => (run program (encodeNat N++(ws.flatten++rest)) f).state≠none) ⊆
      (Finset.univ.filter fun f : Fin (s+delay N ws)→Bool => p (f∘e)) from by
    intro f hf
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hf ⊢
    intro hn
    apply hf
    have ht : (List.ofFn f).take s=List.ofFn (f∘e) := by
      rw [List.ofFn_add]
      simp only [List.take_append,List.length_ofFn,Nat.sub_self,List.take_zero,List.append_nil]
      rw [List.take_of_length_le (by simp)]
      congr 2
    exact finishes_after N ws rest (List.ofFn f) s hlen htotal (by rw [List.length_ofFn]; exact le_refl _) (by
      rw [ht]
      exact hn))

theorem stack_summable (N : ℕ) (ws : List (List Bool)) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1) :
    Summable (tail program (encodeNat N++(ws.flatten++rest))) := by
  apply (summable_nat_add_iff (delay N ws)).1
  exact (WeightedSampler.stored_summable N (ws.flatten++rest)).of_nonneg_of_le
    (fun _ => IntegerDraw.tail_nonneg _ _ _) (fun s => tail_delay N ws rest hlen htotal s)

theorem stack_expected (N : ℕ) (ws : List (List Bool)) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1) :
    (∑' s,tail program (encodeNat N++(ws.flatten++rest)) s)≤
      35*(N.size:ℝ)+21+delay N ws := by
  have hp := stack_summable N ws rest hlen htotal
  rw [← hp.sum_add_tsum_nat_add (delay N ws)]
  have hb : (∑ s∈Finset.range (delay N ws),tail program (encodeNat N++(ws.flatten++rest)) s)≤(delay N ws:ℝ) := by
    calc
      _ ≤ ∑ s∈Finset.range (delay N ws),(1:ℝ) := Finset.sum_le_sum fun _ _ => IntegerDraw.tail_le_one _ _ _
      _ = _ := by simp
  have hs := WeightedSampler.stored_summable N (ws.flatten++rest)
  have he : (∑' s,tail program (encodeNat N++(ws.flatten++rest)) (s+delay N ws)) ≤
      ∑' s,tail draw (encodeNat N++(ws.flatten++rest)) s := by
    exact ((summable_nat_add_iff _).2 hp).tsum_le_tsum
      (fun s => tail_delay N ws rest hlen htotal s) hs
  have hw := WeightedSampler.stored_expected N (ws.flatten++rest)
  linarith

def machine : Machine := compile program

 

theorem charged_time (N : ℕ) (ws : List (List Bool)) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1) :
    Summable (machine.tail (encodeNat N++(ws.flatten++rest))) ∧
      Tendsto (machine.tail (encodeNat N++(ws.flatten++rest))) atTop (nhds 0) ∧
      (∑' s,machine.tail (encodeNat N++(ws.flatten++rest)) s)≤
        70*(N.size:ℝ)+42+2*delay N ws := by
  have hs := stack_summable N ws rest hlen htotal
  have hc := tail_summable_compile program _ hs
  refine ⟨hc,hc.tendsto_atTop_zero,?_⟩
  change (∑' s,(compile program).tail _ s)≤_
  rw [expected_compile program _ hs]
  have he := stack_expected N ws rest hlen htotal
  linarith

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

 

 

namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
noncomputable section

 
theorem live_fold (P : Program) (q : ℕ) (start : Fin q) (code : Fin q→Op q P.work)
    (cfg : Config P) (xs : List Bool)
    (h : (xs.foldl (fun c b => step P b c) cfg).state≠none) :
    xs.foldl (fun c b => step (Sequence.program P q start code) b c) (Sequence.left P q start code cfg)=
      Sequence.left P q start code (xs.foldl (fun c b => step P b c) cfg) := by
  induction xs generalizing cfg with
  | nil => rfl
  | cons a xs ih =>
    have hc : cfg.state≠none := by
      intro hn
      have hz := Sequence.halted_fold P cfg hn (a::xs)
      exact h (by rw [hz]; exact hn)
    simp only [List.foldl_cons]
    rw [Sequence.step_left P q start code cfg a hc]
    exact ih _ h

 
theorem live_left (cfg : Config draw) (xs : List Bool)
    (h : (xs.foldl (fun c b => step draw b c) cfg).state≠none) :
    xs.foldl (fun c b => step program b c) (Sequence.left draw post.labels post.start post.code cfg)=
      Sequence.left draw post.labels post.start post.code (xs.foldl (fun c b => step draw b c) cfg) :=
  live_fold draw post.labels post.start post.code cfg xs h

theorem first_returned (xs : List Bool) (input : List Bool)
    (h : (xs.foldl (fun c b => step program b c) (initial program input)).state=none) :
    (xs.foldl (fun c b => step draw b c) (initial draw input)).state=none := by
  by_contra hn
  have he := live_left (initial draw input) xs hn
  change xs.foldl (fun c b => step program b c) (initial program input)=_ at he
  rw [he] at h
  change Sequence.next (Fin.castAdd post.labels) (some (Fin.natAdd draw.labels post.start)) _=none at h
  cases hc : (xs.foldl (fun c b => step draw b c) (initial draw input)).state <;> simp [Sequence.next,hc] at h

theorem word_injective (N : ℕ) : Function.Injective (fun u : Fin (N+1) => (IntegerDraw.integerWord N u).reverse) := by
  intro u v h
  apply Fin.ext
  have hh := congrArg (fun xs => BinaryTrial.beValue xs.reverse) h
  simpa using hh

 

theorem completes (N : ℕ) (ws : List (List Bool)) (rest xs : List Bool) (s j : ℕ) (u : Fin (N+1))
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1)
    (hl : s+delay N ws≤xs.length)
    (hh : ((xs.take s).foldl (fun c x => step draw x c) (initial draw (encodeNat N++(ws.flatten++rest)))).state=none)
    (hu : ((xs.take s).foldl (fun c x => step draw x c) (initial draw (encodeNat N++(ws.flatten++rest)))).memory.stack 5=
      (IntegerDraw.integerWord N u).reverse)
    (hscan : Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j) :
    (xs.foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))).state=none ∧
    (xs.foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))).memory.outputRev=List.replicate j false := by
  obtain ⟨a,z,haz,hfirst,he⟩ := Sequence.first_prefix draw _ (xs.take s) hh
  obtain ⟨t,k,v,ht,hk,hscanf,hv,hr⟩ := after_first N ws rest a hlen htotal hfirst
  have he' := congrArg (fun c : Config draw => c.memory.stack 5) he
  have hvu : v=u := word_injective N (hv.symm.trans (he'.trans hu))
  subst v
  have hkj : k=j := Option.some.inj (hscanf.symm.trans hscan)
  subst k
  have ha : a.length ≤ s := by
    have h₁ := congrArg List.length haz
    have h₂ := List.length_take_le s xs
    simp only [List.length_append] at h₁
    omega
  have hpre : xs.take a.length=a := by
    have h₁ := congrArg (List.take a.length) haz
    simpa [List.take_take,Nat.min_eq_left ha] using h₁
  let b := (xs.drop a.length).take t
  let c := (xs.drop a.length).drop t
  have hb : b.length=t := by
    simp only [b,List.length_take,List.length_drop]
    dsimp only [delay] at hl
    exact Nat.min_eq_left (by omega)
  have hdecomp : xs=(a++b)++c := by
    rw [List.append_assoc]
    change xs=a++((xs.drop a.length).take t++(xs.drop a.length).drop t)
    rw [List.take_append_drop]
    exact (List.take_append_drop a.length xs).symm.trans (congrArg (fun z => z++xs.drop a.length) hpre)
  obtain ⟨hd,ho⟩ := hr b hb
  rw [hdecomp,List.foldl_append,Sequence.halted_fold program _ hd c]
  exact ⟨hd,ho⟩

 

theorem halted_output (N : ℕ) (ws : List (List Bool)) (rest xs : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1)
    (hh : (xs.foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))).state=none) :
    ∃ (j : ℕ) (u : Fin (N+1)),j<ws.length ∧
      Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j ∧
      (xs.foldl (fun c x => step draw x c) (initial draw (encodeNat N++(ws.flatten++rest)))).memory.stack 5=
        (IntegerDraw.integerWord N u).reverse ∧
      (xs.foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))).memory.outputRev=List.replicate j false := by
  have hf := first_returned xs _ hh
  obtain ⟨a,z,haz,hfirst,he⟩ := Sequence.first_prefix draw _ xs hf
  obtain ⟨t,j,u,ht,hj,hscan,hu,hr⟩ := after_first N ws rest a hlen htotal hfirst
  have heu := (congrArg (fun c : Config draw => c.memory.stack 5) he).symm.trans hu
  let ys := xs++List.replicate (delay N ws) false
  have htake : ys.take xs.length=xs := by simp [ys]
  have hc := completes N ws rest ys xs.length j u hlen htotal (by simp [ys])
    (by rw [htake]; exact hf) (by rw [htake]; exact heu) hscan
  have hp : ys.foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest)))=
      xs.foldl (fun c x => step program x c) (initial program (encodeNat N++(ws.flatten++rest))) := by
    dsimp only [ys]
    rw [List.foldl_append,Sequence.halted_fold program _ hh]
  exact ⟨j,u,hj,hscan,heu,by rw [← hp]; exact hc.2⟩

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

end

end OAI
