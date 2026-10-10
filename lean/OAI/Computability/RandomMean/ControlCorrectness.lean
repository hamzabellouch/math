import OAI.Computability.RandomMean.Control

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

abbrev VecsRep {n B : ℕ} (I : SolveBox n B) (vs : List (BoxVector I)) (rs : List (List W)) :=
  List.Forall₂ (fun v r => VectorRep v.val r) vs rs

theorem VecsRep.map {n B : ℕ} {I : SolveBox n B} {vs : List (BoxVector I)} {rs : List (List W)}
    (h : VecsRep I vs rs) : VectorsRep (vs.map Subtype.val) rs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h hr ih => exact List.Forall₂.cons h ih

theorem VecsRep.getD {n B : ℕ} {I : SolveBox n B} {vs : List (BoxVector I)} {rs : List (List W)}
    (h : VecsRep I vs rs) (i : ℕ) (d : BoxVector I) {ds : List W} (hd : VectorRep d.val ds) :
    VectorRep (vs.getD i d).val (rs.getD i ds) := by
  induction h generalizing i with
  | nil => simpa using hd
  | cons h hr ih => cases i with
    | zero => exact h
    | succ i => exact ih i

structure EnvRep (G : Game) (B : ℕ) (e : Env) : Prop where
  graph : ∃ w : Fin G.m→W, e.1=Graph.codeVertices G w ∧ ∀ i, (w i).val=transformed G i
  exponent : e.2.1.length=sampleExponent B
  samples : e.2.2.1.length=globalS B
  trials : e.2.2.2.1.length=globalJ G.n B
  basic : G.n*(128*globalS B)≤e.2.2.2.2.length

def JobPackRep {G : Game} {B : ℕ} {A : SourceControl.Result G B} (j : SourceControl.Job G B A) (z : Pack) : Prop :=
  match j with
  | .solve P I | .ask P I | .orient P _ I | .orientPlus P _ I | .tighten P _ I _ =>
      RawBudget.Rep P z.p ∧ RawBox.Rep I z.b
  | .trials P I J | .orientTrials P _ I J => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.t.length=J
  | .update P _ I _ v => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ VectorRep v.val z.q
  | .centers P _ I _ t v => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.t.length=t ∧ VectorRep v.val z.q
  | .reweight P _ I side hs => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.o.1=side ∧
      List.Forall₂ (fun H r => MaskRep H.val r) hs z.o.2

def FramePackRep {G : Game} {B : ℕ} {A C : SourceControl.Result G B} (f : SourceControl.Frame G B A C) (z : Pack) : Prop :=
  match f with
  | .trialsHead P I J | .orientHead P _ I J => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.t.length=J
  | .vectorCons v => VectorRep v.val z.q
  | .median I => RawBox.Rep I z.b
  | .centerFirst P _ I _ v => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ VectorRep v.val z.q
  | .centerSecond I _ _ r => RawBox.Rep I z.b ∧ VectorRep r.val z.r
  | .centersHead P _ I _ t v => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.t.length=t ∧ VectorRep v.val z.q
  | .orientLoop P _ I _ | .tightenFirst P _ I _ | .tightenSecond P _ I _ |
    .solveTight P _ I _ | .solveOriented P _ I _ => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b
  | .orientTail H N => z.o.2.length=2 ∧ MaskRep H.val (z.o.2.headD []) ∧ MaskRep N.val (z.o.2.tail.headD [])
  | .orientCons O => RawOrientation.Rep O z.o
  | .combine _ | .includeInner _ => True
  | .floor _ _ | .ceiling _ _ => True
  | .reweightHead P _ I side hs => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.o.1=side ∧
      List.Forall₂ (fun H r => MaskRep H.val r) hs z.o.2
  | .solveReweighted P _ I _ side => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.o.1=side
  | .capHigh I _ rs | .capLow I _ rs => VecsRep I rs z.vs

def ValueRep {G : Game} {B : ℕ} (A : SourceControl.Result G B) (v : A.Value) (z : Pack) : Prop :=
  match A,v with
  | .vector _,v => VectorRep v.val z.q
  | .vectors I,vs => VecsRep I vs z.vs
  | .orientation _,O => RawOrientation.Rep O z.o
  | .orientations _,Os => RawOrientation.ManyRep Os z.os
  | .inner _,T => RawBox.Rep T.box z.b

inductive KontRep {G : Game} {B : ℕ} : {A R : SourceControl.Result G B} → SourceControl.Kont G B A R → List Cell → Prop where
  | done {A} : KontRep (SourceControl.Kont.done (R:=A)) []
  | push {A C R} {f : SourceControl.Frame G B A C} {k : SourceControl.Kont G B C R} {c : Cell} {ks : List Cell}
      (tag : c.1.length=f.tag.val) (frame : FramePackRep f c.2) (tail : KontRep k ks) : KontRep (.push f k) (c::ks)

inductive StateRep {G : Game} {B : ℕ} {R : SourceControl.Result G B} : SourceControl.State G B R → State → Prop where
  | call {A} {j : SourceControl.Job G B A} {k : SourceControl.Kont G B A R} {c : Cell} {ks : List Cell}
      (tag : c.1.length=j.tag.val) (job : JobPackRep j c.2) (stack : KontRep k ks) : StateRep (.call j k) (c,ks)
  | ret {A} {k : SourceControl.Kont G B A R} {v : A.Value} {c : Cell} {ks : List Cell}
      (tag : c.1.length=10) (value : ValueRep A v c.2) (stack : KontRep k ks) : StateRep (.ret k v) (c,ks)

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

variable {G : Game} {B : ℕ} {x : Input}

theorem smallWidth_eq (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) : smallWidth b x=decide (I.width≤128*globalS B) := by
  change Word.le ((b x).1,RawBudget.times 128 (Counter.word x.1.2.2.1))=_
  rw [Word.le_eval,RawBudget.times_val,Counter.word_val,hb.width,he.samples]
  rw [mul_comm (globalS B : ℤ) 128]
  change decide ((I.width:ℤ)≤((128*globalS B:ℕ):ℤ))=_
  exact decide_eq_decide.mpr Int.ofNat_le

theorem basic_rep (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) (hsmall : I.width≤128*globalS B) :
    VectorRep (I.exactVector G).val (basic b x) := by
  obtain ⟨ws,hw,heval⟩ := he.graph
  change VectorRep _ (RawBasic.solve ((x.1.1,b x),x.1.2.2.2.2))
  rw [hw]
  exact RawBasic.solve_rep G hb ws heval _ ((Nat.mul_le_mul_left G.n hsmall).trans he.basic)

theorem narrow_rep (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) {v : Fin G.n→ℤ} (q : Code Input (List W)) (hq : VectorRep v (q x))
    (hB : 128*globalS B<I.width) : RawBox.Rep (I.narrowCentered hB v) (narrow b q x) := by
  apply RawBox.centered_rep v hq
  apply RawBox.dividedWidth_nat hb _ (32*globalS B)
  change 2^(Counter.add (x.1.2.1,List.replicate 5 ())).length=32*globalS B
  simp [Counter.add,Code.append_eval,List.length_append,he.exponent,pow_add,globalS,Nat.mul_comm]

theorem wide_rep {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) {v : Fin G.n→ℤ} (q : Code Input (List W)) (hq : VectorRep v (q x))
    (hB : 128*globalS B<I.width) : RawBox.Rep (I.wideCentered hB v) (wide b q x) := by
  apply RawBox.centered_rep v hq
  exact RawBox.dividedWidth_nat hb _ 8 (by norm_num)

theorem delta_eq (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) : (delta b x).val=I.delta := by
  apply RawBox.dividedWidth_nat hb _ (4*globalS B)
  change 2^(Counter.add (x.1.2.1,List.replicate 2 ())).length=4*globalS B
  simp [Counter.add,Code.append_eval,List.length_append,he.exponent,pow_add,globalS,Nat.mul_comm]

theorem capWidth_eq (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) : (capWidth b x).val=I.C := by
  change (Word.sub ((b x).1,delta b x)).val=_
  rw [Word.sub_val,hb.width,delta_eq he b hb]
  exact (Int.ofNat_sub (Nat.div_le_self I.width (4*globalS B))).symm

theorem centerAt_rep {I : SolveBox G.n B} {rs : List (BoxVector I)}
    (hb : RawBox.Rep I (caller x).b) (hv : VecsRep I rs (current x).vs) (i : Code Input Count) :
    VectorRep (rs.getD (i x).length I.midpoint).val (centerAt i x) := by
  change VectorRep _ (Code.getD [] (((current x).vs,i x),RawBox.midpoint (caller x).b))
  rw [Code.getD_eval]
  exact hv.getD _ _ (RawBox.midpoint_rep hb)

theorem lastPositive_rep (he : EnvRep G B x.1) {I : SolveBox G.n B} {rs : List (BoxVector I)}
    (hb : RawBox.Rep I (caller x).b) (hv : VecsRep I rs (current x).vs) :
    MaskRep (PositiveDisplacement I (rs.getD (globalS B) I.midpoint)) (lastPositive x) := by
  have hv' := centerAt_rep hb hv (env ≫ₚ samples)
  change VectorRep (rs.getD x.1.2.2.1.length I.midpoint).val _ at hv'
  rw [he.samples] at hv'
  apply RawOrientation.positives_rep hb _ hv' _
  change (Counter.word x.1.2.2.1).val=_
  rw [Counter.word_val,he.samples]

theorem lastNegative_rep (he : EnvRep G B x.1) {I : SolveBox G.n B} {rs : List (BoxVector I)}
    (hb : RawBox.Rep I (caller x).b) (hv : VecsRep I rs (current x).vs) :
    MaskRep (NegativeDisplacement I (rs.getD (globalS B) I.midpoint)) (lastNegative x) := by
  have hv' := centerAt_rep hb hv (env ≫ₚ samples)
  change VectorRep (rs.getD x.1.2.2.1.length I.midpoint).val _ at hv'
  rw [he.samples] at hv'
  apply RawOrientation.negatives_rep hb _ hv' _
  change (Counter.word x.1.2.2.1).val=_
  rw [Counter.word_val,he.samples]

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

noncomputable def jobCode {G : Game} {B : ℕ} {A : SourceControl.Result G B} (j : SourceControl.Job G B A) : Code Input State :=
  match j with
  | .solve .. => solveCase | .ask .. => askCase | .trials .. => trialsCase | .update .. => updateCase
  | .centers .. => centersCase | .orient .. => orientCase | .orientTrials .. => orientTrialsCase
  | .orientPlus .. => orientPlusCase | .tighten .. => tightenCase | .reweight .. => reweightCase

theorem dispatch_call {G : Game} {B : ℕ} {A : SourceControl.Result G B} (j : SourceControl.Job G B A)
    (e : Env) (r : Count) (c : Cell) (ks : List Cell) (ht : c.1.length=j.tag.val) :
    dispatch (e,r,(c,ks))=jobCode j (e,r,(c,ks)) := by
  cases j <;> simp [dispatch,Code.select_eval,state,ht,SourceControl.Job.tag,jobCode,List.getD]

theorem sampled_call_rep {G : Game} {B : ℕ} {A R : SourceControl.Result G B}
    (j : SourceControl.Job G B A) (k : SourceControl.Kont G B A R)
    (e : Env) (he : EnvRep G B e) (r : Count) (c : Cell) (ks : List Cell)
    (ht : c.1.length=j.tag.val) (hj : JobPackRep j c.2) (hk : KontRep k ks) :
    StateRep (SourceControl.sampledStep r.length (.call j k)) (dispatch (e,r,(c,ks))) := by
  rw [dispatch_call j e r c ks ht]
  cases j with
  | solve P I =>
    obtain ⟨hp,hb⟩ := hj
    have hs := RawBudget.small_eq hp
    have hw := smallWidth_eq (x:=(e,r,(c,ks))) he (current ≫ₚ b) hb
    simp only [SourceControl.sampledStep,jobCode,solveCase,Code.branch_eval,Code.comp_eval,p_eval]
    change StateRep (if hR : P.parameter<1 then _ else _) (if RawBudget.small c.2.p then _ else _)
    by_cases hR : P.parameter<1
    · rw [dite_eq_left hR,hs,ite_eq_left (by simp [hR])]
      exact StateRep.ret (by rfl) (RawBox.smallVector_rep hb hp) hk
    · rw [dite_eq_right hR,hs,ite_eq_right (by simp [hR])]
      by_cases hB : I.width≤128*globalS B
      · rw [dite_eq_left hB,hw,ite_eq_left (by simp [hB])]
        exact StateRep.ret (by rfl) (basic_rep he (current ≫ₚ b) hb hB) hk
      · rw [dite_eq_right hB,hw,ite_eq_right (by simp [hB])]
        exact StateRep.call (by rfl) ⟨hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb⟩ hk)
  | ask P I =>
    obtain ⟨hp,hb⟩ := hj
    exact StateRep.call (by rfl) ⟨hp,hb,he.trials⟩ (KontRep.push (by rfl) hb hk)
  | trials P I J =>
    obtain ⟨hp,hb,htime⟩ := hj
    cases J with
    | zero =>
      have hz : c.2.t=[] := List.length_eq_zero_iff.mp htime
      simp only [SourceControl.sampledStep,jobCode,trialsCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      simp only [hz,List.isEmpty_nil,ite_true]
      exact StateRep.ret (by rfl) List.Forall₂.nil hk
    | succ J =>
      have hz : c.2.t.isEmpty=false := by cases h : c.2.t <;> simp_all
      simp only [SourceControl.sampledStep,jobCode,trialsCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      rw [hz,ite_eq_right Bool.noConfusion]
      exact StateRep.call (by rfl) ⟨hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb,by change c.2.t.tail.length = _; simp [List.length_tail,htime]⟩ hk)
  | update P hR I hB v =>
    obtain ⟨hp,hb,hv⟩ := hj
    exact StateRep.call (by rfl) ⟨RawBudget.reduceK_rep hp,narrow_rep he (current ≫ₚ b) hb (current ≫ₚ q) hv hB⟩
      (KontRep.push (by rfl) ⟨hp,hb,hv⟩ hk)
  | centers P hR I hB t v =>
    obtain ⟨hp,hb,htime,hv⟩ := hj
    cases t with
    | zero =>
      have hz : c.2.t=[] := List.length_eq_zero_iff.mp htime
      simp only [SourceControl.sampledStep,jobCode,centersCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      simp only [hz,List.isEmpty_nil,ite_true]
      exact StateRep.ret (by rfl) (List.Forall₂.cons hv List.Forall₂.nil) hk
    | succ t =>
      have hz : c.2.t.isEmpty=false := by cases h : c.2.t <;> simp_all
      simp only [SourceControl.sampledStep,jobCode,centersCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      rw [hz,ite_eq_right Bool.noConfusion]
      exact StateRep.call (by rfl) ⟨hp,hb,hv⟩ (KontRep.push (by rfl) ⟨hp,hb,by change c.2.t.tail.length = _; simp [List.length_tail,htime],hv⟩ hk)
  | orient P hR I =>
    obtain ⟨hp,hb⟩ := hj
    have hw := smallWidth_eq (x:=(e,r,(c,ks))) he (current ≫ₚ b) hb
    simp only [SourceControl.sampledStep,jobCode,orientCase,Code.branch_eval]
    rw [hw]
    by_cases hB : I.width≤128*globalS B
    · rw [dite_eq_left hB,ite_eq_left (by simp [hB])]
      exact StateRep.ret (by rfl) (RawOrientation.base_rep G hb hp (basic_rep he (current ≫ₚ b) hb hB)) hk
    · rw [dite_eq_right hB,ite_eq_right (by simp [hB])]
      exact StateRep.call (by rfl) ⟨hp,hb,he.samples,RawBox.midpoint_rep hb⟩ (KontRep.push (by rfl) ⟨hp,hb⟩ hk)
  | orientTrials P hR I J =>
    obtain ⟨hp,hb,htime⟩ := hj
    cases J with
    | zero =>
      have hz : c.2.t=[] := List.length_eq_zero_iff.mp htime
      simp only [SourceControl.sampledStep,jobCode,orientTrialsCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      simp only [hz,List.isEmpty_nil,ite_true]
      exact StateRep.ret (by rfl) List.Forall₂.nil hk
    | succ J =>
      have hz : c.2.t.isEmpty=false := by cases h : c.2.t <;> simp_all
      simp only [SourceControl.sampledStep,jobCode,orientTrialsCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      rw [hz,ite_eq_right Bool.noConfusion]
      exact StateRep.call (by rfl) ⟨hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb,by change c.2.t.tail.length = _; simp [List.length_tail,htime]⟩ hk)
  | orientPlus P hR I =>
    obtain ⟨hp,hb⟩ := hj
    exact StateRep.call (by rfl) ⟨hp,hb,he.trials⟩ (KontRep.push (by rfl) trivial hk)
  | tighten P hR I hB =>
    obtain ⟨hp,hb⟩ := hj
    exact StateRep.call (by rfl) ⟨RawBudget.reduceK_rep hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb⟩ hk)
  | reweight P hR I side Hs =>
    obtain ⟨hp,hb,hside,hs⟩ := hj
    cases Hs with
    | nil =>
      have ho := List.forall₂_nil_left_iff.mp hs
      simp only [SourceControl.sampledStep,jobCode,reweightCase,Code.branch_eval,Code.comp_eval,o_eval,Code.snd_eval,Code.empty_eval]
      change StateRep _ (if c.2.o.2.isEmpty then _ else _)
      simp only [ho,List.isEmpty_nil,ite_true]
      exact StateRep.ret (by rfl) List.Forall₂.nil hk
    | cons H Hs =>
      obtain ⟨rh,rt,hmask,htail,ho⟩ := List.forall₂_cons_left_iff.mp hs
      simp only [SourceControl.sampledStep,jobCode,reweightCase,Code.branch_eval,Code.comp_eval,o_eval,Code.snd_eval,Code.empty_eval]
      change StateRep _ (if c.2.o.2.isEmpty then _ else _)
      simp only [ho,List.isEmpty_cons]
      refine StateRep.call (by rfl) ⟨?_,hb⟩ (KontRep.push (by rfl) ⟨hp,hb,hside,?_⟩ hk)
      · change RawBudget.Rep (if side then P.reweightM H.val else P.reweightK H.val)
          (if c.2.o.1 then RawBudget.reweightM (c.2.p,c.2.o.2.headD []) else RawBudget.reweightK (c.2.p,c.2.o.2.headD []))
        rw [hside,ho]
        cases side
        · exact RawBudget.reweightK_rep hp hmask
        · exact RawBudget.reweightM_rep hp hmask
      · change List.Forall₂ _ Hs c.2.o.2.tail
        rw [ho]
        exact htail

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

noncomputable def frameCode {G : Game} {B : ℕ} {A C : SourceControl.Result G B}
    (f : SourceControl.Frame G B A C) : Code Input State :=
  match f with
  | .trialsHead .. => trialsHeadCase | .vectorCons .. => vectorConsCase | .median .. => medianCase
  | .centerFirst .. => centerFirstCase | .centerSecond .. => centerSecondCase | .centersHead .. => centersHeadCase
  | .orientLoop .. => orientLoopCase | .orientTail .. => orientTailCase | .orientHead .. => orientHeadCase
  | .orientCons .. => orientConsCase | .combine .. => combineCase | .tightenFirst .. => tightenFirstCase
  | .tightenSecond .. => tightenSecondCase | .floor .. => boxPassCase | .ceiling .. => boxPassCase
  | .solveTight .. => solveTightCase | .solveOriented .. => solveOrientedCase | .reweightHead .. => reweightHeadCase
  | .solveReweighted .. => solveReweightedCase | .capHigh .. => capHighCase | .capLow .. => capLowCase
  | .includeInner .. => includeInnerCase

theorem dispatch_return {G : Game} {B : ℕ} {A C : SourceControl.Result G B} (f : SourceControl.Frame G B A C)
    (e : Env) (r : Count) (c d : Cell) (ks : List Cell) (ht : c.1.length=10) (hf : d.1.length=f.tag.val) :
    dispatch (e,r,(c,d::ks))=frameCode f (e,r,(c,d::ks)) := by
  cases f <;> simp [dispatch,Code.select_eval,state,ht,resume,stack,hf,SourceControl.Frame.tag,frameCode,List.getD,Code.empty_eval]

theorem sampled_resume_rep {G : Game} {B : ℕ} {A C R : SourceControl.Result G B}
    (f : SourceControl.Frame G B A C) (v : A.Value) (k : SourceControl.Kont G B C R)
    (e : Env) (he : EnvRep G B e) (r : Count) (c d : Cell) (ks : List Cell)
    (hf : FramePackRep f d.2) (hv : ValueRep A v c.2) (hk : KontRep k ks) :
    StateRep (SourceControl.sampledResume f v k r.length) (frameCode f (e,r,(c,d::ks))) := by
  cases f with
  | trialsHead P I J =>
    obtain ⟨hp,hb,hj⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hb,hj⟩ (KontRep.push (by rfl) hv hk)
  | vectorCons a => exact StateRep.ret (by rfl) (List.Forall₂.cons hf hv) hk
  | median I => exact StateRep.ret (by rfl) (RawMedian.boxed_rep hf v hv.map) hk
  | centerFirst P hR I hB q =>
    obtain ⟨hp,hb,hq⟩ := hf
    exact StateRep.call (by rfl) ⟨RawBudget.reduceM_rep hp,narrow_rep he (caller ≫ₚ b) hb (caller ≫ₚ RawControl.q) hq hB⟩
      (KontRep.push (by rfl) ⟨hb,hv⟩ hk)
  | centerSecond I hB q r' =>
    obtain ⟨hb,hr⟩ := hf
    exact StateRep.ret (by rfl) (RawBox.average_rep hb hr hv) hk
  | centersHead P hR I hB t q =>
    obtain ⟨hp,hb,ht,hq⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hb,ht,hv⟩ (KontRep.push (by rfl) hq hk)
  | orientLoop P hR I hB =>
    obtain ⟨hp,hb⟩ := hf
    have hpos := lastPositive_rep (x:=(e,r,(c,d::ks))) he hb hv
    have hneg := lastNegative_rep (x:=(e,r,(c,d::ks))) he hb hv
    have hpTest := RawBudget.measureLarge_eq G.positive hp hpos
    have hnTest := RawBudget.measureLarge_eq G.positive hp hneg
    simp only [SourceControl.sampledResume,frameCode,orientLoopCase,Code.branch_eval,Code.comp_eval,Code.pair_eval,p_eval]
    change StateRep (if hh : (1/2:ℚ)<P.measure _ then _ else _)
      (if RawBudget.measureLarge (d.2.p,lastPositive (e,r,(c,d::ks))) then _ else _)
    by_cases hH : (1/2:ℚ)<P.measure (PositiveDisplacement I (v.getD (globalS B) I.midpoint))
    · rw [dite_eq_left hH,hpTest,decide_eq_true hH,ite_eq_left rfl]
      exact StateRep.ret (by rfl) ⟨rfl,List.Forall₂.cons (Array.complement_rep hpos) List.Forall₂.nil⟩ hk
    · rw [dite_eq_right hH,hpTest,decide_eq_false hH,ite_eq_right (by decide)]
      change StateRep _ (if RawBudget.measureLarge (d.2.p,lastNegative (e,r,(c,d::ks))) then _ else _)
      by_cases hN : (1/2:ℚ)<P.measure (NegativeDisplacement I (v.getD (globalS B) I.midpoint))
      · rw [dite_eq_left hN,hnTest,decide_eq_true hN,ite_eq_left rfl]
        exact StateRep.ret (by rfl) ⟨rfl,List.Forall₂.cons (Array.complement_rep hneg) List.Forall₂.nil⟩ hk
      · rw [dite_eq_right hN,hnTest,decide_eq_false hN,ite_eq_right (by decide)]
        exact StateRep.call (by rfl)
          ⟨hp,wide_rep (caller ≫ₚ b) hb (centerAt random) (centerAt_rep (x:=(e,r,(c,d::ks))) hb hv random) hB⟩
          (KontRep.push (by rfl) ⟨rfl,hpos,hneg⟩ hk)
  | orientTail H N =>
    obtain ⟨_,hH,hN⟩ := hf
    exact StateRep.ret (by rfl) (RawOrientation.extend_rep hv H N hH hN) hk
  | orientHead P hR I J =>
    obtain ⟨hp,hb,hj⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hb,hj⟩ (KontRep.push (by rfl) hv hk)
  | orientCons O => exact StateRep.ret (by rfl) (List.Forall₂.cons hf hv) hk
  | combine P => exact StateRep.ret (by rfl) (RawOrientation.combine_rep hv) hk
  | tightenFirst P hR I hB =>
    obtain ⟨hp,hb⟩ := hf
    have hd := delta_eq (x:=(e,r,(c,d::ks))) he (caller ≫ₚ b) hb
    have hm := RawBox.movedFloor_eq hb hv (delta (caller ≫ₚ b) (e,r,(c,d::ks)))
    rw [hd] at hm
    simp only [SourceControl.sampledResume,frameCode,tightenFirstCase,Code.branch_eval]
    change StateRep (if h : ∃ i, (I.delta:ℤ)≤v.val i-I.a i then _ else _)
      (if RawBox.movedFloor (d.2.b,c.2.q,delta (caller ≫ₚ b) (e,r,(c,d::ks))) then _ else _)
    rw [hm]
    by_cases h : ∃ i, (I.delta:ℤ)≤v.val i-I.a i
    · simp only [dite_eq_left h,decide_eq_true h,ite_true]
      exact StateRep.call (by rfl) ⟨hp,RawBox.floor_rep hb v hv⟩ (KontRep.push (by rfl) trivial hk)
    · simp only [dite_eq_right h,decide_eq_false h]
      exact StateRep.call (by rfl) ⟨RawBudget.reduceM_rep hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb⟩ hk)
  | tightenSecond P hR I hB =>
    obtain ⟨hp,hb⟩ := hf
    have hd := delta_eq (x:=(e,r,(c,d::ks))) he (caller ≫ₚ b) hb
    have hm := RawBox.movedCeiling_eq hb hv (delta (caller ≫ₚ b) (e,r,(c,d::ks)))
    rw [hd] at hm
    simp only [SourceControl.sampledResume,frameCode,tightenSecondCase,Code.branch_eval]
    change StateRep (if h : ∃ i, (I.delta:ℤ)≤I.b i-v.val i then _ else _)
      (if RawBox.movedCeiling (d.2.b,c.2.q,delta (caller ≫ₚ b) (e,r,(c,d::ks))) then _ else _)
    rw [hm]
    by_cases h : ∃ i, (I.delta:ℤ)≤I.b i-v.val i
    · simp only [dite_eq_left h,decide_eq_true h,ite_true]
      exact StateRep.call (by rfl) ⟨hp,RawBox.ceiling_rep hb v hv⟩ (KontRep.push (by rfl) trivial hk)
    · simp only [dite_eq_right h,decide_eq_false h]
      exact StateRep.ret (by rfl) hb hk
  | floor I q => exact StateRep.ret (by rfl) hv hk
  | ceiling I q => exact StateRep.ret (by rfl) hv hk
  | solveTight P hR I hB =>
    obtain ⟨hp,_⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hv⟩ (KontRep.push (by rfl) ⟨hp,hv⟩ (KontRep.push (by rfl) trivial hk))
  | solveOriented P hR I hB =>
    obtain ⟨hp,hb⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hb,hv.1,hv.2⟩ (KontRep.push (by rfl) ⟨hp,hb,hv.1⟩ hk)
  | reweightHead P hR I side Hs =>
    exact StateRep.call (by rfl) hf (KontRep.push (by rfl) hv hk)
  | solveReweighted P hR I hB side =>
    obtain ⟨hp,hb,hs⟩ := hf
    have hc := capWidth_eq (x:=(e,r,(c,d::ks))) he (caller ≫ₚ b) hb
    simp only [SourceControl.sampledResume,frameCode,solveReweightedCase,Code.branch_eval]
    change StateRep (if side then _ else _) (if d.2.o.1 then _ else _)
    rw [hs]
    cases side with
    | false =>
      exact StateRep.call (by rfl) ⟨hp,RawBox.capLow_rep hb _ _ _ hc⟩ (KontRep.push (by rfl) hv hk)
    | true =>
      exact StateRep.call (by rfl) ⟨hp,RawBox.capHigh_rep hb _ _ _ hc⟩ (KontRep.push (by rfl) hv hk)
  | capHigh I hB rs =>
    exact StateRep.ret (by rfl) (Array.foldMin_rep (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le v) hv hf.map) hk
  | capLow I hB rs =>
    exact StateRep.ret (by rfl) (Array.foldMax_rep (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le v) hv hf.map) hk
  | includeInner T => exact StateRep.ret (by rfl) hv hk

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

theorem sampled_dispatch_rep {G : Game} {B : ℕ} {R : SourceControl.Result G B}
    {s : SourceControl.State G B R} {z : State} (h : StateRep s z)
    (e : Env) (he : EnvRep G B e) (r : Count) :
    StateRep (SourceControl.sampledStep r.length s) (dispatch (e,r,z)) := by
  cases h with
  | call ht hj hk => exact sampled_call_rep _ _ e he r _ _ ht hj hk
  | ret ht hv hk =>
    cases hk with
    | done =>
      simpa [dispatch,Code.select_eval,state,ht,resume,stack,Code.empty_eval,SourceControl.sampledStep,List.getD]
        using StateRep.ret ht hv KontRep.done
    | push hf hfr hk =>
      rw [dispatch_return _ e r _ _ _ ht hf]
      exact sampled_resume_rep _ _ _ e he r _ _ _ hfr hv hk

end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
