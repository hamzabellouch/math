import Mathlib
import OAI.Probability.Contingency.GreedyTable
import OAI.Probability.Contingency.StackSafety

namespace OAI

/-! Binary Addition. -/

noncomputable section


namespace Contingency.BitModel.StackCode.BinaryAdd
open BinarySubtract
noncomputable section

theorem value_append (as bs : List Bool) :
    value (as++bs)=value as+2^as.length*value bs := by
  induction as with
  | nil => simp [value]
  | cons a as ih =>
    simp only [List.cons_append,value,List.length_cons,pow_succ,ih]
    ring

theorem full_output_value (ds : List Digit) (c : Bool) :
    value (output ds c++[carry ds c])=value (ds.map Digit.a)+value (ds.map Digit.b)+c.toNat := by
  rw [value_append,output_length]
  simpa only [value,Nat.mul_zero,Nat.add_zero] using (word_identity ds c).symm

 

theorem add_tape (ds : List Digit) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b)
    (h2 : m.stack 2=[]) :
    ∃ m' : Memory 4,m'.stack 0=[] ∧ m'.stack 1=[] ∧
      (m'.stack 2).length=ds.length+1 ∧
      value (m'.stack 2).reverse=value (ds.map Digit.a)+value (ds.map Digit.b) ∧
      m'.stack 3=m.stack 3 ∧ m'.input=m.input ∧ m'.outputRev=m.outputRev ∧
      ∀ coins : Fin ((3*ds.length+3)*2)→Bool,
        (List.ofFn coins).foldl (fun cfg b => (compile program).step b cfg)
          (encode program (config (.start false) m))=encode program ⟨none,m'⟩ := by
  let m' := ((wordMemory ds false m).pop 0).push 2 (carry ds false)
  have hf := wordMemory_stacks ds false m ha hb
  have h0 : m'.stack 0=[] := by simp [m',Memory.push,Memory.pop,hf.1]
  have h1 : m'.stack 1=[] := by simpa [m',Memory.push,Memory.pop] using hf.2.1
  have ho : m'.stack 2=carry ds false::(output ds false).reverse := by
    simp [m',Memory.push,Memory.pop,hf.2.2.1,h2]
  have h3 : m'.stack 3=m.stack 3 := by simpa [m',Memory.push,Memory.pop] using hf.2.2.2.1
  refine ⟨m',h0,h1,?_,?_,h3,hf.2.2.2.2.1,hf.2.2.2.2.2,?_⟩
  · simp [ho,output_length]
  · rw [ho,List.reverse_cons,List.reverse_reverse]
    simpa using full_output_value ds false
  · intro coins
    rw [BinarySubtract.fold_compiled]
    rw [fold_independent _ (List.replicate (3*ds.length+3) false) (by simp)]
    have hr := finish_run ds false m ha hb (List.replicate (3*ds.length) false) (by simp) false false false
    have he : List.replicate (3*ds.length+3) false=List.replicate (3*ds.length) false++[false,false,false] := by
      rw [List.replicate_add]; rfl
    rw [he,hr]

 

theorem add_naturals (x y n : ℕ) (hx : x.size≤n) (hy : y.size≤n) (m : Memory 4)
    (h0 : m.stack 0=bits n x) (h1 : m.stack 1=bits n y) (h2 : m.stack 2=[]) :
    ∃ m' : Memory 4,value (m'.stack 2).reverse=x+y ∧ (m'.stack 2).length=n+1 ∧
      ∀ coins : Fin ((3*n+3)*2)→Bool,
        (List.ofFn coins).foldl (fun cfg b => (compile program).step b cfg)
          (encode program (config (.start false) m))=encode program ⟨none,m'⟩ := by
  let ds := digits (bits n x) (bits n y)
  have hl : (bits n x).length=(bits n y).length := by rw [bits_length _ _ (Nat.size_le.mp hx),bits_length _ _ (Nat.size_le.mp hy)]
  obtain ⟨ha,hb,hd⟩ := digits_maps (bits n x) (bits n y) hl
  obtain ⟨m',_,_,hm,he,_,_,_,hr⟩ := add_tape ds m (h0.trans ha.symm) (h1.trans hb.symm) h2
  have hn : ds.length=n := hd.trans (bits_length n x (Nat.size_le.mp hx))
  refine ⟨m',?_,by simpa [hn] using hm,?_⟩
  · simpa [ds,ha,hb,bits_value] using he
  · let S : ℕ→Prop := fun T => ∀ coins : Fin T→Bool,
        (List.ofFn coins).foldl (fun cfg b => (compile program).step b cfg)
          (encode program (config (.start false) m))=encode program ⟨none,m'⟩
    have hr' : S ((3*ds.length+3)*2) := hr
    have ht : (3*ds.length+3)*2=(3*n+3)*2 := by rw [hn]
    exact Eq.mp (congrArg S ht) hr' 

end
end Contingency.BitModel.StackCode.BinaryAdd

 

 

 

namespace Contingency.BitModel.StackCode.WeightedScan
open BinarySubtract
noncomputable section

inductive Q
  | start (c : Bool)
  | read (c a : Bool)
  | place (c a b : Bool)
  | advance
  | restore
  | back (b : Bool)
  | selected
  | out
  | finish
  deriving DecidableEq, Fintype

def label (q : Q) : Fin (Fintype.card Q) := Fintype.equivFin Q q

def code : Q→Op (Fintype.card Q) 4
  | .start c => .pop 0 (label (if c then .selected else .advance)) (label (.read c false)) (label (.read c true))
  | .read c a => .read (label (.place c a false)) (label (.place c a false)) (label (.place c a true))
  | .place c a b => .push 2 (outBit a b c) (label (.start (nextBorrow a b c)))
  | .advance => .push 3 false (label .restore)
  | .restore => .pop 2 (label (.start false)) (label (.back false)) (label (.back true))
  | .back b => .push 0 b (label .restore)
  | .selected => .pop 3 (label .finish) (label .out) (label .out)
  | .out => .emit false (label .selected)
  | .finish => .halt

def program : Program := ⟨Fintype.card Q,4,label (.start false),fun pc => code ((Fintype.equivFin Q).symm pc)⟩
def config (q : Q) (m : Memory 4) : Config program := ⟨some (label q),m⟩

def exec (t : ℕ) (cfg : Config program) : Config program :=
  (List.replicate t false).foldl (fun cfg b => step program b cfg) cfg

theorem exec_add (s t : ℕ) (cfg : Config program) : exec (s+t) cfg=exec t (exec s cfg) := by
  simp only [exec,List.replicate_add,List.foldl_append]

@[simp] theorem exec_zero (cfg : Config program) : exec 0 cfg=cfg := rfl
@[simp] theorem exec_one (cfg : Config program) : exec 1 cfg=step program false cfg := rfl

theorem one_step (q : Q) (m : Memory 4) (coin : Bool) :
    step program coin (config q m)=⟨(effect (code q) coin m).1,(effect (code q) coin m).2⟩ := by
  simp [step,program,config,label]

theorem first_step (m : Memory 4) (c a coin : Bool) (as : List Bool) (ha : m.stack 0=a::as) :
    step program coin (config (.start c) m)=config (.read c a) (m.pop 0) := by
  rw [one_step]
  cases a <;> simp [code,effect,branch,ha,config] <;> rfl

theorem second_step (m : Memory 4) (c a b coin : Bool) (bs : List Bool) (hb : m.input=b::bs) :
    step program coin (config (.read c a) m)=config (.place c a b) m.read := by
  rw [one_step]
  cases b <;> simp [code,effect,branch,hb,config] <;> rfl

theorem third_step (m : Memory 4) (c a b coin : Bool) :
    step program coin (config (.place c a b) m)=config (.start (nextBorrow a b c)) (m.push 2 (outBit a b c)) := by
  rw [one_step]; rfl

def digitMemory (d : Digit) (c : Bool) (m : Memory 4) : Memory 4 :=
  ((m.pop 0).read).push 2 (outBit d.a d.b c)

def wordMemory : List Digit→Bool→Memory 4→Memory 4
  | [],_,m => m
  | d::ds,c,m => wordMemory ds (nextBorrow d.a d.b c) (digitMemory d c m)

theorem three_steps (m : Memory 4) (d : Digit) (c : Bool) (as bs : List Bool)
    (ha : m.stack 0=d.a::as) (hb : m.input=d.b::bs) :
    exec 3 (config (.start c) m)=config (.start (nextBorrow d.a d.b c)) (digitMemory d c m) := by
  change step program false (step program false (step program false (config (.start c) m)))=_
  rw [first_step m c d.a false as ha,second_step _ c d.a d.b false bs,third_step]
  · rfl
  · exact hb

theorem pass (ds : List Digit) (c : Bool) (m : Memory 4) (rest : List Bool)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.input=ds.map Digit.b++rest) :
    exec (3*ds.length) (config (.start c) m)=config (.start (borrow ds c)) (wordMemory ds c m) := by
  induction ds generalizing c m with
  | nil => rfl
  | cons d ds ih =>
    have he : 3*(d::ds).length=3+3*ds.length := by simp; omega
    rw [he,exec_add,three_steps m d c _ _ ha hb,ih]
    · rfl
    · simp [digitMemory,Memory.push,Memory.pop,Memory.read,ha]
    · simp [digitMemory,Memory.push,Memory.pop,Memory.read,hb]

theorem wordMemory_stacks (ds : List Digit) (c : Bool) (m : Memory 4) (rest : List Bool)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.input=ds.map Digit.b++rest) :
    (wordMemory ds c m).stack 0=[] ∧
    (wordMemory ds c m).stack 2=(output ds c).reverse++m.stack 2 ∧
    (wordMemory ds c m).stack 3=m.stack 3 ∧
    (wordMemory ds c m).input=rest ∧
    (wordMemory ds c m).outputRev=m.outputRev := by
  induction ds generalizing c m with
  | nil => exact ⟨ha,rfl,rfl,hb,rfl⟩
  | cons d ds ih =>
    have h0 : (digitMemory d c m).stack 0=ds.map Digit.a := by
      simp [digitMemory,Memory.push,Memory.pop,Memory.read,ha]
    have hi : (digitMemory d c m).input=ds.map Digit.b++rest := by
      simp [digitMemory,Memory.push,Memory.pop,Memory.read,hb]
    have hh := ih (nextBorrow d.a d.b c) (digitMemory d c m) h0 hi
    refine ⟨hh.1,?_,?_,hh.2.2.2.1,hh.2.2.2.2⟩
    · simpa [wordMemory,output,List.reverse_cons,List.append_assoc,digitMemory,Memory.push,Memory.pop,Memory.read] using hh.2.1
    · simpa [wordMemory,digitMemory,Memory.push,Memory.pop,Memory.read] using hh.2.2.1

end
end Contingency.BitModel.StackCode.WeightedScan

 

 

namespace Contingency.BitModel.StackCode.WeightedScan
open BinarySubtract
noncomputable section

theorem end_word (m : Memory 4) (c : Bool) (h0 : m.stack 0=[]) :
    exec 1 (config (.start c) m)=config (if c then .selected else .advance) (m.pop 0) := by
  rw [exec_one,one_step]
  simp [code,effect,branch,h0,config]; rfl

theorem advance (m : Memory 4) :
    exec 1 (config .advance m)=config .restore (m.push 3 false) := by
  rw [exec_one,one_step]; rfl

theorem restore_empty (m : Memory 4) (h2 : m.stack 2=[]) :
    exec 1 (config .restore m)=config (.start false) (m.pop 2) := by
  rw [exec_one,one_step]
  simp [code,effect,branch,h2,config]; rfl

theorem restore_bit (m : Memory 4) (b : Bool) (bs : List Bool) (h2 : m.stack 2=b::bs) :
    exec 2 (config .restore m)=config .restore ((m.pop 2).push 0 b) := by
  change step program false (step program false (config .restore m))=_
  rw [one_step]
  have he : (⟨(effect (code .restore) false m).1,(effect (code .restore) false m).2⟩ : Config program)=
      config (.back b) (m.pop 2) := by
    cases b <;> simp [code,effect,branch,h2,config] <;> rfl
  rw [he,one_step]
  rfl

def restoreMemory : List Bool→Memory 4→Memory 4
  | [],m => m.pop 2
  | b::bs,m => restoreMemory bs ((m.pop 2).push 0 b)

theorem restore_run (bs : List Bool) (m : Memory 4) (h2 : m.stack 2=bs) :
    exec (2*bs.length+1) (config .restore m)=config (.start false) (restoreMemory bs m) := by
  induction bs generalizing m with
  | nil => exact restore_empty m h2
  | cons b bs ih =>
    have he : 2*(b::bs).length+1=2+(2*bs.length+1) := by simp; omega
    rw [he,exec_add,restore_bit m b bs h2,ih]
    · rfl
    · simp [Memory.push,Memory.pop,h2]

theorem restoreMemory_stacks (bs : List Bool) (m : Memory 4) (h2 : m.stack 2=bs) :
    (restoreMemory bs m).stack 0=bs.reverse++m.stack 0 ∧
    (restoreMemory bs m).stack 2=[] ∧
    (restoreMemory bs m).stack 3=m.stack 3 ∧
    (restoreMemory bs m).input=m.input ∧
    (restoreMemory bs m).outputRev=m.outputRev := by
  induction bs generalizing m with
  | nil => simp [restoreMemory,Memory.pop,h2]
  | cons b bs ih =>
    have hh := ih ((m.pop 2).push 0 b) (by simp [Memory.pop,Memory.push,h2])
    simpa [restoreMemory,Memory.pop,Memory.push,List.reverse_cons,List.append_assoc] using hh

theorem selected_empty (m : Memory 4) (h3 : m.stack 3=[]) :
    exec 2 (config .selected m)=⟨none,m.pop 3⟩ := by
  change step program false (step program false (config .selected m))=_
  rw [one_step]
  have he : (⟨(effect (code .selected) false m).1,(effect (code .selected) false m).2⟩ : Config program)=
      config .finish (m.pop 3) := by
    simp [code,effect,branch,h3,config]; rfl
  rw [he,one_step]
  rfl

def emitMemory (m : Memory 4) : Memory 4 :=
  {m.pop 3 with outputRev:=false::m.outputRev}

theorem selected_bit (m : Memory 4) (bs : List Bool) (h3 : m.stack 3=false::bs) :
    exec 2 (config .selected m)=config .selected (emitMemory m) := by
  change step program false (step program false (config .selected m))=_
  rw [one_step]
  have he : (⟨(effect (code .selected) false m).1,(effect (code .selected) false m).2⟩ : Config program)=
      config .out (m.pop 3) := by
    simp [code,effect,branch,h3,config]; rfl
  rw [he,one_step]
  rfl

def selectedMemory : ℕ→Memory 4→Memory 4
  | 0,m => m.pop 3
  | i+1,m => selectedMemory i (emitMemory m)

theorem selected_run (i : ℕ) (m : Memory 4) (h3 : m.stack 3=List.replicate i false) :
    exec (2*i+2) (config .selected m)=⟨none,selectedMemory i m⟩ := by
  induction i generalizing m with
  | zero => exact selected_empty m h3
  | succ i ih =>
    have he : 2*(i+1)+2=2+(2*i+2) := by omega
    rw [he,exec_add,selected_bit m (List.replicate i false) h3,ih]
    · rfl
    · simp [emitMemory,Memory.pop,h3,List.replicate_succ]

theorem selectedMemory_output (i : ℕ) (m : Memory 4) :
    (selectedMemory i m).outputRev=List.replicate i false++m.outputRev := by
  induction i generalizing m with
  | zero => rfl
  | succ i ih =>
    rw [selectedMemory,ih]
    change List.replicate i false++false::m.outputRev=_
    rw [show List.replicate (i+1) false=List.replicate i false++[false] by rw [List.replicate_add]; rfl,List.append_assoc]
    rfl

 

theorem skip_weight (ds : List Digit) (m : Memory 4) (rest : List Bool) (i : ℕ)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.input=ds.map Digit.b++rest)
    (h2 : m.stack 2=[]) (h3 : m.stack 3=List.replicate i false)
    (hsub : value (ds.map Digit.b)≤value (ds.map Digit.a)) :
    ∃ m', exec (5*ds.length+3) (config (.start false) m)=config (.start false) m' ∧
      m'.stack 0=output ds false ∧ m'.stack 2=[] ∧
      m'.stack 3=List.replicate (i+1) false ∧ m'.input=rest ∧ m'.outputRev=m.outputRev := by
  let w := wordMemory ds false m
  have hw := wordMemory_stacks ds false m rest ha hb
  have hc := (subtract_correct ds hsub).1
  let a := (w.pop 0).push 3 false
  have ha2 : a.stack 2=(output ds false).reverse := by
    simpa [a,Memory.push,Memory.pop,h2,w] using hw.2.1
  have hr := restoreMemory_stacks (output ds false).reverse a ha2
  refine ⟨restoreMemory (output ds false).reverse a,?_,?_,hr.2.1,?_,?_,?_⟩
  · have he : 5*ds.length+3=3*ds.length+1+1+(2*(output ds false).reverse.length+1) := by simp; omega
    rw [he,exec_add (3*ds.length+1+1) (2*(output ds false).reverse.length+1),exec_add (3*ds.length+1) 1,exec_add (3*ds.length) 1,pass ds false m rest ha hb,hc,end_word _ false hw.1]
    change exec (2*(output ds false).reverse.length+1) (exec 1 (config .advance (w.pop 0)))=_
    rw [advance,restore_run _ _ ha2]
  · simpa [a,Memory.push,Memory.pop,w,hw.1] using hr.1
  · have hm3 : a.stack 3=List.replicate (i+1) false := by
      simp [a,Memory.push,Memory.pop,w,hw.2.2.1,h3,List.replicate_succ]
    exact hr.2.2.1.trans hm3
  · exact hr.2.2.2.1.trans hw.2.2.2.1
  · exact hr.2.2.2.2.trans hw.2.2.2.2

 
theorem hit_weight (ds : List Digit) (m : Memory 4) (rest : List Bool) (i : ℕ)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.input=ds.map Digit.b++rest)
    (h3 : m.stack 3=List.replicate i false)
    (hlt : value (ds.map Digit.a)<value (ds.map Digit.b)) :
    ∃ m', exec (3*ds.length+2*i+3) (config (.start false) m)=⟨none,m'⟩ ∧
      m'.outputRev=List.replicate i false++m.outputRev := by
  let w := wordMemory ds false m
  have hw := wordMemory_stacks ds false m rest ha hb
  have hc := (borrow_iff ds).mpr hlt
  have hwi : (w.pop 0).stack 3=List.replicate i false := by
    simpa [w,Memory.pop,hw.2.2.1] using h3
  refine ⟨selectedMemory i (w.pop 0),?_,?_⟩
  · have he : 3*ds.length+2*i+3=(3*ds.length+1)+(2*i+2) := by omega
    rw [he,exec_add (3*ds.length+1) (2*i+2),exec_add (3*ds.length) 1,pass ds false m rest ha hb,hc,end_word _ true hw.1]
    exact selected_run i (w.pop 0) hwi
  · rw [selectedMemory_output]
    exact congrArg (List.append (List.replicate i false)) hw.2.2.2.2

end
end Contingency.BitModel.StackCode.WeightedScan

 

 

 

namespace Contingency.BitModel.StackCode.WeightedScan
open BinarySubtract
noncomputable section

def weightTotal (ws : List (List Bool)) : ℕ := (ws.map value).sum

def indexedWeights : List (List Bool)→ℕ→List (ℕ×ℕ)
  | [],_ => []
  | w::ws,i => (i,value w)::indexedWeights ws (i+1)

@[simp] theorem indexed_total (ws : List (List Bool)) (i : ℕ) :
    Contingency.IntegerDraw.total (indexedWeights ws i)=weightTotal ws := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih => simp [indexedWeights,Contingency.IntegerDraw.total,weightTotal,ih]

 

theorem scan_run (ws : List (List Bool)) (as : List Bool) (m : Memory 4)
    (rest : List Bool) (i : ℕ)
    (hlen : ∀ w∈ws,w.length=as.length)
    (ha : m.stack 0=as) (hi : m.input=ws.flatten++rest)
    (h2 : m.stack 2=[]) (h3 : m.stack 3=List.replicate i false)
    (hz : value as<weightTotal ws) :
    ∃ (j : ℕ) (m' : Memory 4), j<ws.length ∧
      Contingency.IntegerDraw.scan (indexedWeights ws i) (value as)=some (i+j) ∧
      exec (3*as.length+2*i+3+j*(5*as.length+5)) (config (.start false) m)=⟨none,m'⟩ ∧
      m'.outputRev=List.replicate (i+j) false++m.outputRev := by
  induction ws generalizing as m i with
  | nil => simp [weightTotal] at hz
  | cons w ws ih =>
    have hw : w.length=as.length := hlen w (by simp)
    let ds := digits as w
    obtain ⟨hda,hdb,hdl⟩ := digits_maps as w hw.symm
    have hha : m.stack 0=ds.map Digit.a := ha.trans hda.symm
    have hhi : m.input=ds.map Digit.b++(ws.flatten++rest) := by
      simpa [ds,hdb,List.flatten_cons,List.append_assoc] using hi
    by_cases hlt : value as<value w
    · obtain ⟨m',hr,ho⟩ := hit_weight ds m (ws.flatten++rest) i hha hhi h3 (by simpa [ds,hda,hdb] using hlt)
      refine ⟨0,m',by simp,?_,?_,?_⟩
      · simp [indexedWeights,Contingency.IntegerDraw.scan,hlt]
      · simpa [ds,hdl] using hr
      · simpa using ho
    · have hsub : value (ds.map Digit.b)≤value (ds.map Digit.a) := by simpa [ds,hda,hdb] using (Nat.le_of_not_gt hlt)
      obtain ⟨m₁,hr,ha₁,h2₁,h3₁,hi₁,ho₁⟩ := skip_weight ds m (ws.flatten++rest) i hha hhi h2 h3 hsub
      have hv := (subtract_correct ds hsub).2
      have hlen₁ : ∀ w∈ws,w.length=(output ds false).length := by
        intro v hv
        simpa [output_length,ds,hdl] using hlen v (by simp [hv])
      have hz₁ : value (output ds false)<weightTotal ws := by
        rw [hv]
        simp only [ds,hda,hdb] at *
        simp only [weightTotal,List.map_cons,List.sum_cons] at hz ⊢
        omega
      obtain ⟨j,m',hj,hscan,hexec,hout⟩ := ih (output ds false) m₁ (i+1) hlen₁ ha₁ hi₁ h2₁ h3₁ hz₁
      refine ⟨j+1,m',by simpa using Nat.succ_lt_succ hj,?_,?_,?_⟩
      · simp only [indexedWeights,Contingency.IntegerDraw.scan,ite_eq_right hlt]
        have he : value (output ds false)=value as-value w := by simpa [ds,hda,hdb] using hv
        rw [he] at hscan
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hscan
      · have he : 3*as.length+2*i+3+(j+1)*(5*as.length+5)=
            (5*ds.length+3)+(3*(output ds false).length+2*(i+1)+3+j*(5*(output ds false).length+5)) := by
          simp only [output_length,ds,hdl]
          ring
        rw [he,exec_add,hr,hexec]
      · simpa [ho₁,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hout

theorem step_independent (cfg : Config program) (b b' : Bool) :
    step program b cfg=step program b' cfg := by
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => rfl
  | some pc =>
    unfold step
    dsimp only [program]
    cases (Fintype.equivFin Q).symm pc <;> rfl

theorem fold_independent (xs ys : List Bool) (hl : xs.length=ys.length) (cfg : Config program) :
    xs.foldl (fun cfg b => step program b cfg) cfg=ys.foldl (fun cfg b => step program b cfg) cfg := by
  induction xs generalizing ys cfg with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
      simp only [List.foldl_cons]
      rw [step_independent _ x y]
      exact ih _ hl _

 

theorem scan_tape (ws : List (List Bool)) (as : List Bool) (m : Memory 4) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=as.length)
    (ha : m.stack 0=as) (hi : m.input=ws.flatten++rest)
    (h2 : m.stack 2=[]) (h3 : m.stack 3=[])
    (hz : value as<weightTotal ws) :
    ∃ (t j : ℕ) (m' : Memory 4), t*2≤10*(as.length+1)*ws.length ∧ j<ws.length ∧
      Contingency.IntegerDraw.scan (indexedWeights ws 0) (value as)=some j ∧
      m'.outputRev=List.replicate j false++m.outputRev ∧
      ∀ coins : Fin (t*2)→Bool,
        (List.ofFn coins).foldl (fun cfg b => (compile program).step b cfg)
          (encode program (config (.start false) m))=encode program ⟨none,m'⟩ := by
  obtain ⟨j,m',hj,hs,hr,ho⟩ := scan_run ws as m rest 0 hlen ha hi h2 h3 hz
  let t := 3*as.length+2*0+3+j*(5*as.length+5)
  refine ⟨t,j,m',?_,hj,by simpa using hs,by simpa using ho,?_⟩
  · have hm := Nat.mul_le_mul_left (5*as.length+5) (Nat.succ_le_iff.mpr hj)
    dsimp only [t]
    nlinarith only [hm]
  · intro coins
    rw [BinarySubtract.fold_compiled]
    have he := fold_independent (List.ofFn fun i : Fin t => coins (second i)) (List.replicate t false) (by simp) (config (.start false) m)
    rw [he]
    change encode program (exec t (config (.start false) m))=_
    rw [hr]

end
end Contingency.BitModel.StackCode.WeightedScan

 

 

 

namespace Contingency.BitModel.StackCode

namespace Internal

def work {w : ℕ} (i : Fin w) : Fin (w+2) := i.castSucc.castSucc

def input (w : ℕ) : Fin (w+2) := (Fin.last w).castSucc

def output (w : ℕ) : Fin (w+2) := Fin.last (w+1)

@[simp] theorem work_inj {w : ℕ} (i j : Fin w) : work i=work j ↔ i=j := by simp [work]
@[simp] theorem work_ne_input {w : ℕ} (i : Fin w) : work i≠input w := by simp [work,input]
@[simp] theorem work_ne_output {w : ℕ} (i : Fin w) : work i≠output w := by simp [work,output]
@[simp] theorem input_ne_output (w : ℕ) : input w≠output w := by simp [input,output]
@[simp] theorem input_ne_work {w : ℕ} (i : Fin w) : input w≠work i := (work_ne_input i).symm
@[simp] theorem output_ne_work {w : ℕ} (i : Fin w) : output w≠work i := (work_ne_output i).symm
@[simp] theorem output_ne_input (w : ℕ) : output w≠input w := (input_ne_output w).symm

def op {l w : ℕ} : Op l w→Op l (w+2)
  | .push i b q => .push (work i) b q
  | .pop i e z o => .pop (work i) e z o
  | .read e z o => .pop (input w) e z o
  | .coin z o => .coin z o
  | .emit b q => .push (output w) b q
  | .jump q => .jump q
  | .halt => .halt

def program (P : Program) : Program := ⟨P.labels,P.work+2,P.start,fun q => op (P.code q)⟩

 

def MemoryRel {w : ℕ} (a : Memory w) (b : Memory (w+2)) : Prop :=
  (∀ i,b.stack (work i)=a.stack i) ∧
    b.stack (input w)=a.input ∧ b.stack (output w)=a.outputRev

theorem push_work {w : ℕ} {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b)
    (i : Fin w) (v : Bool) : MemoryRel (a.push i v) (b.push (work i) v) := by
  rcases h with ⟨hw,hi,ho⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    simp [Memory.push,Function.update_apply,hw]
  · simpa [Memory.push] using hi
  · simpa [Memory.push] using ho

theorem pop_work {w : ℕ} {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b)
    (i : Fin w) : MemoryRel (a.pop i) (b.pop (work i)) := by
  rcases h with ⟨hw,hi,ho⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    simp [Memory.pop,Function.update_apply,hw]
  · simpa [Memory.pop] using hi
  · simpa [Memory.pop] using ho

theorem read_input {w : ℕ} {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b) :
    MemoryRel a.read (b.pop (input w)) := by
  rcases h with ⟨hw,hi,ho⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    simpa [Memory.pop,Memory.read] using hw j
  · simp [Memory.pop,Memory.read,hi]
  · simpa [Memory.pop,Memory.read] using ho

theorem emit_output {w : ℕ} {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b) (v : Bool) :
    MemoryRel {a with outputRev:=v::a.outputRev} (b.push (output w) v) := by
  rcases h with ⟨hw,hi,ho⟩
  refine ⟨?_,?_,?_⟩
  · intro j
    simpa [Memory.push] using hw j
  · simpa [Memory.push] using hi
  · simp [Memory.push,ho]

theorem effect_rel {l w : ℕ} (code : Op l w) (coin : Bool)
    {a : Memory w} {b : Memory (w+2)} (h : MemoryRel a b) :
    (effect (op code) coin b).1=(effect code coin a).1 ∧
      MemoryRel (effect code coin a).2 (effect (op code) coin b).2 := by
  cases code with
  | push i v q => exact ⟨rfl,push_work h i v⟩
  | pop i e z o => exact ⟨by simp [op,effect,h.1 i],pop_work h i⟩
  | read e z o => exact ⟨by simp [op,effect,h.2.1],read_input h⟩
  | coin z o => exact ⟨rfl,h⟩
  | emit v q => exact ⟨rfl,emit_output h v⟩
  | jump q => exact ⟨rfl,h⟩
  | halt => exact ⟨rfl,h⟩

def ConfigRel (P : Program) (a : Config P) (b : Config (program P)) : Prop :=
  b.state=a.state ∧ MemoryRel a.memory b.memory

theorem step_rel (P : Program) (coin : Bool) {a : Config P} {b : Config (program P)}
    (h : ConfigRel P a b) : ConfigRel P (step P coin a) (step (program P) coin b) := by
  rcases a with ⟨sa,ma⟩
  rcases b with ⟨sb,mb⟩
  obtain ⟨hs,hm⟩ := h
  dsimp only at hs hm
  subst sb
  cases sa with
  | none => exact ⟨rfl,hm⟩
  | some pc => exact effect_rel (P.code pc) coin hm

theorem fold_rel (P : Program) (coins : List Bool) {a : Config P} {b : Config (program P)}
    (h : ConfigRel P a b) :
    ConfigRel P (coins.foldl (fun c v => step P v c) a)
      (coins.foldl (fun c v => step (program P) v c) b) := by
  induction coins generalizing a b with
  | nil => exact h
  | cons v coins ih => exact ih (step_rel P v h)

 

def loaded (P : Program) (xs : List Bool) (external : Memory (P.work+2)) : Config (program P) :=
  ⟨some P.start,{external with stack:=Fin.lastCases [] (Fin.lastCases xs (fun _ => []))}⟩

theorem loaded_rel (P : Program) (xs : List Bool) (external : Memory (P.work+2)) :
    ConfigRel P (initial P xs) (loaded P xs external) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro i
    simp [loaded,initial,work]
  · simp [loaded,initial,input]
  · simp [loaded,initial,output]

 

theorem loaded_run (P : Program) (xs : List Bool) (external : Memory (P.work+2))
    {t : ℕ} (coins : Fin t→Bool) :
    ConfigRel P (run P xs coins)
      ((List.ofFn coins).foldl (fun c v => step (program P) v c) (loaded P xs external)) :=
  fold_rel P _ (loaded_rel P xs external)

end Internal
end Contingency.BitModel.StackCode

 

 

namespace Contingency.BitModel.StackCode.Internal

theorem effect_frame {l w : ℕ} (code : Op l w) (coin : Bool) (b : Memory (w+2)) :
    (effect (op code) coin b).2.input=b.input ∧
      (effect (op code) coin b).2.outputRev=b.outputRev ∧
      (effect (op code) coin b).2.consumed=b.consumed := by
  cases code <;> exact ⟨rfl,rfl,rfl⟩

theorem step_frame (P : Program) (coin : Bool) (b : Config (program P)) :
    (step (program P) coin b).memory.input=b.memory.input ∧
      (step (program P) coin b).memory.outputRev=b.memory.outputRev ∧
      (step (program P) coin b).memory.consumed=b.memory.consumed := by
  rcases b with ⟨s,m⟩
  cases s with
  | none => exact ⟨rfl,rfl,rfl⟩
  | some q => exact effect_frame (P.code q) coin m

theorem fold_frame (P : Program) (coins : List Bool) (b : Config (program P)) :
    (coins.foldl (fun c v => step (program P) v c) b).memory.input=b.memory.input ∧
    (coins.foldl (fun c v => step (program P) v c) b).memory.outputRev=b.memory.outputRev ∧
    (coins.foldl (fun c v => step (program P) v c) b).memory.consumed=b.memory.consumed := by
  induction coins generalizing b with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons c coins ih =>
    have hh := ih (step (program P) c b)
    have he := step_frame P c b
    exact ⟨hh.1.trans he.1,hh.2.1.trans he.2.1,hh.2.2.trans he.2.2⟩

theorem tape_fold (P : Program) (cfg : Config P) {t : ℕ} (coins : Fin (t*2)→Bool) :
    (List.ofFn coins).foldl (fun cfg b => (compile P).step b cfg) (encode P cfg)=
      encode P ((List.ofFn (fun i : Fin t => coins (second i))).foldl (fun cfg b => step P b cfg) cfg) := by
  rw [coins_as_pairs,fold_pairs]
  congr 1
  have hh := List.foldl_map (f:=Prod.snd) (g:=fun cfg b => step P b cfg)
    (l:=List.ofFn fun i : Fin t => (coins (first i),coins (second i))) (init:=cfg)
  simpa only [List.map_ofFn,Function.comp_def] using hh.symm

 

theorem loaded_tape (P : Program) (xs : List Bool) (external : Memory (P.work+2))
    {t : ℕ} (coins : Fin (t*2)→Bool) :
    ∃ b : Config (program P),
      (List.ofFn coins).foldl (fun cfg v => (compile (program P)).step v cfg)
          (encode (program P) (loaded P xs external))=encode (program P) b ∧
      b.state=(run P xs (fun i : Fin t => coins (second i))).state ∧
      (∀ i,b.memory.stack (work i)=(run P xs (fun i : Fin t => coins (second i))).memory.stack i) ∧
      b.memory.stack (input P.work)=(run P xs (fun i : Fin t => coins (second i))).memory.input ∧
      b.memory.stack (output P.work)=(run P xs (fun i : Fin t => coins (second i))).memory.outputRev ∧
      b.memory.input=external.input ∧ b.memory.outputRev=external.outputRev ∧
      b.memory.consumed=external.consumed := by
  let bs := List.ofFn fun i : Fin t => coins (second i)
  let b := bs.foldl (fun c v => step (program P) v c) (loaded P xs external)
  have hr := loaded_run P xs external (fun i : Fin t => coins (second i))
  have hf := fold_frame P bs (loaded P xs external)
  exact ⟨b,tape_fold (program P) (loaded P xs external) coins,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,hf.1,hf.2.1,hf.2.2⟩

end Contingency.BitModel.StackCode.Internal

end

end OAI
