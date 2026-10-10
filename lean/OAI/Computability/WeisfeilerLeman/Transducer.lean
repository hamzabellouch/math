import OAI.Computability.WeisfeilerLeman.Diagonal

namespace OAI

universe uK uA uT

namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem tm_integer_lower (k : ℕ) (hk : 100000000 ≤ k) (c : Convention) (p : InputClass) (A : TM)
    (hA : Decides (.turing A) c k p) :
    ∃ n₀,∀ n ≥ n₀,n^(k/1000) < worstTime (.turing A) p n := by
  let s := k/16
  let d := 3*s+6
  let q := k-d-conventionShift c
  let U := Universal.machine s
  let C := coefficient U d q (d+q+2)
  have hshift : 1 ≤ conventionShift c ∧ conventionShift c ≤ 2 := by cases c <;> decide
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hdim : k=d+q+conventionShift c := by dsimp [d,q,s]; omega
  have hq : d+3 ≤ q := by dsimp [q,d,s]; omega
  have ha : 2*max 2400 (8*(k/1000)+1)+3 ≤ s := by
    rcases max_cases 2400 (8*(k/1000)+1) with ⟨he,_⟩ | ⟨he,_⟩ <;> rw [he] <;> dsimp [s] <;> omega
  have hCpos : 1 ≤ C := coefficient_pos U d q
  obtain ⟨mfit,hfit⟩ := designation_small U d q A
  let m₀ := mfit+384*C^3+128+C+(body U d q).charge+consumerFactor U d q A+
    (8*A.tapes+2)+(8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2)+18*s
  refine ⟨baseOrder U d q m₀,?_⟩
  intro n hn
  let m := Numeric.chooseOrder C n
  have hchoice := Numeric.chooseOrder_bounds C n m₀ hCpos hn
  have hm : m₀ ≤ m := hchoice.1
  have hbase : baseOrder U d q m ≤ n := hchoice.2.1
  have hmn : n ≤ m^8 := Numeric.order_polynomial C n m hCpos (by dsimp [m₀] at hm; omega) hchoice.2.2
  apply lt_of_not_ge
  exact tm_pointwise s d q k (k/1000) n m c p A hA hdim
    (by dsimp [m₀] at hm; omega) hs rfl hq ha hbase hmn
    (hfit m (by dsimp [m₀] at hm; omega) n hmn)
    (by change C≤ m; dsimp only [m₀] at hm; omega)
    (by change (body U d q).charge≤ m; dsimp only [m₀] at hm; omega)
    (by change consumerFactor U d q A≤ m; dsimp only [m₀] at hm; omega)
    (by dsimp [m₀] at hm; omega)
    (by dsimp [m₀] at hm; omega)
    (by dsimp [m₀] at hm; omega)

 theorem tm_real_lower (k : ℕ) (hk : 100000000 ≤ k) (c : Convention) (p : InputClass) (A : TM)
    (hA : Decides (.turing A) c k p) :
    ∃ n₀ : ℕ,∀ n : ℕ, n ≥ n₀ → (n : ℝ)^((1/2000 : ℝ)*(k : ℝ)) ≤ (worstTime (.turing A) p n : ℝ) := by
  obtain ⟨n₀,hn₀⟩ := tm_integer_lower k hk c p A hA
  refine ⟨n₀+1,?_⟩
  intro n hn
  have hint := hn₀ n (by omega)
  have hexp : (1/2000 : ℝ)*(k : ℝ) ≤ (k/1000 : ℕ) := by
    have h : k ≤ 2000*(k/1000) := by omega
    have hr : (k : ℝ) ≤ 2000*((k/1000 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  calc
    _ ≤ (n : ℝ)^((k/1000 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) hexp
    _ = (n : ℝ)^(k/1000) := Real.rpow_natCast _ _
    _ ≤ (worstTime (.turing A) p n : ℝ) := by exact_mod_cast hint.le
end WLTime

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} {T : Type uT} [DecidableEq K] [DecidableEq T]
def casesList (select : Tops K A → T) (body : T → Code K A) : List T → Code K A
  | [] => .skip
  | x::xs => .branch (fun v => decide (select v=x)) (body x) (casesList select body xs)
 theorem casesList_exec (select : Tops K A → T) (body : T → Code K A) (xs : List T)
    {s t out} (hx : select (tops s)∈xs) (he : (body (select (tops s))).Exec s t out) :
    ∃u ≤ t+xs.length,(casesList select body xs).Exec s u out := by
  induction xs with
  | nil => simp at hx
  | cons x xs ih =>
    by_cases h : select (tops s)=x
    · refine ⟨t+1,by simp,?_⟩
      exact .branch_true (by simpa using h) (h ▸ he)
    · have hm : select (tops s)∈xs := (List.mem_cons.mp hx).resolve_left h
      obtain ⟨u,hu,he'⟩ := ih hm
      exact ⟨u+1,by simp only [List.length_cons]; omega,.branch_false (by simpa using h) he'⟩
noncomputable def casesAll [Fintype T] (select : Tops K A → T) (body : T → Code K A) : Code K A :=
  casesList select body Finset.univ.toList
 theorem casesAll_exec [Fintype T] (select : Tops K A → T) (body : T → Code K A)
    {s t out} (he : (body (select (tops s))).Exec s t out) :
    ∃u ≤ t+Fintype.card T,(casesAll select body).Exec s u out := by
  simpa only [Finset.length_toList,Finset.card_univ,casesAll] using
    casesList_exec select body Finset.univ.toList (by simp) he
end WLTime.TypedStack.Code

namespace WLTime
instance instFintypeMove : Fintype Move := ⟨{.left,.stay,.right},by intro d; cases d <;> simp⟩
end WLTime

namespace WLTime.TMTransducer
open TypedStack
variable (M : TM)
abbrev Letter := Fin M.symbols ⊕ Fin M.states ⊕ Move
abbrev Reg := Fin 2 ⊕ (Fin M.tapes × Bool)
def stateReg : Reg M := .inl 0
def historyReg : Reg M := .inl 1
def symbolDecode : Letter M → Fin M.symbols
  | .inl x => x
  | _ => TMStack.blank M
def stateDecode : Option (Letter M) → Fin M.states
  | some (.inr (.inl q)) => q
  | _ => ⟨0,by have := M.states_ge; omega⟩
def store (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) : Stacks (Reg M) (Letter M) :=
  Sum.elim (fun i => if i.val=0 then [.inr (.inl q)] else ds.map (fun d => .inr (.inr d)))
    (Code.listMap Sum.inl (TMStack.store s))
abbrev Key := Fin M.states × (Fin M.tapes → Fin M.symbols)
def select (v : Tops (Reg M) (Letter M)) : Key M :=
  (stateDecode M (v (stateReg M)),fun a => ((v (.inr (a,true))).map (symbolDecode M)).getD (TMStack.blank M))
def live (v : Tops (Reg M) (Letter M)) : Bool := decide
  (¬((select M v).1.val=1 ∨ (select M v).1.val=2))
def stepBody (p : TMStack.Payload M) : Code (Reg M) (Letter M) :=
  .seq (((TMStack.stepCode M p).mapLetters Sum.inl (symbolDecode M)).relabel Sum.inr)
    (.seq (.pop (stateReg M)) (.seq (.push (stateReg M) (.inr (.inl p.1)))
      (.push (historyReg M) (.inr (.inr (p.2.2 ⟨0,M.tapes_pos⟩))))))
noncomputable def step : Code (Reg M) (Letter M) :=
  .casesAll (select M) (fun x => stepBody M (M.transition x.1 x.2))
noncomputable def runCode : Code (Reg M) (Letter M) := .loop (live M) (step M)

 theorem select_store (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) :
    select M (tops (store M q s ds))=(q,fun a => (s a).right.headD (TMStack.blank M)) := by
  apply Prod.ext
  · rfl
  · funext a
    change (((s a).right.map Sum.inl).head?.map (symbolDecode M)).getD (TMStack.blank M)=(s a).right.headD (TMStack.blank M)
    cases (s a).right <;> rfl

 theorem body_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (p : TMStack.Payload M) :
    (stepBody M p).Exec (store M q s ds) (TMStack.bodyCost p.2.2 (List.finRange M.tapes)+6)
      (store M p.1 (TMStack.nextTapes M p s) (p.2.2 ⟨0,M.tapes_pos⟩::ds)) := by
  have hb := Code.mapLetters_exec (Sum.inl : Fin M.symbols → Letter M) (symbolDecode M)
    (by intro x; rfl) (TMStack.stepCode_exec M p s)
  have he := Code.relabel_inr_exec hb
    (fun i : Fin 2 => if i.val=0 then [Sum.inr (Sum.inl q)] else ds.map (fun d => Sum.inr (Sum.inr d)))
  let mid := store M q (TMStack.nextTapes M p s) ds
  have hp := Code.Exec.pop mid (stateReg M)
  have hq := Code.Exec.push (Function.update mid (stateReg M) (mid (stateReg M)).tail)
    (stateReg M) (Sum.inr (Sum.inl p.1))
  have hd := Code.Exec.push
    (Function.update (Function.update mid (stateReg M) (mid (stateReg M)).tail)
      (stateReg M) (Sum.inr (Sum.inl p.1)::(mid (stateReg M)).tail))
    (historyReg M) (Sum.inr (Sum.inr (p.2.2 ⟨0,M.tapes_pos⟩)))
  have hex := Code.Exec.seq he (Code.Exec.seq hp (Code.Exec.seq hq hd))
  unfold stepBody
  convert hex using 1 <;> try rfl
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr k => rfl

noncomputable def stepFactor : ℕ := 8*M.tapes+Fintype.card (Key M)+8
 theorem step_exec (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (hr : TMStack.Relative M C s) :
    ∃u ≤ stepFactor M-1,(step M).Exec (store M C.state s ds) u
      (store M (M.transition C.state (fun a => C.tape a (C.head a))).1
        (TMStack.nextTapes M (M.transition C.state (fun a => C.tape a (C.head a))) s)
        ((M.transition C.state (fun a => C.tape a (C.head a))).2.2 ⟨0,M.tapes_pos⟩::ds)) := by
  have hs : select M (tops (store M C.state s ds))=(C.state,fun a => C.tape a (C.head a)) := by
    rw [select_store]
    congr 1
    funext a
    have h := hr a 0
    simpa only [TapePair.contents_zero,add_zero] using h
  have hb := body_exec M C.state s ds (M.transition C.state (fun a => C.tape a (C.head a)))
  change ((fun x : Key M => stepBody M (M.transition x.1 x.2))
    (C.state,fun a => C.tape a (C.head a))).Exec _ _ _ at hb
  rw [←hs] at hb
  obtain ⟨u,hu,he⟩ := Code.casesAll_exec (select M) (fun x => stepBody M (M.transition x.1 x.2)) hb
  refine ⟨u,?_,he⟩
  have ht := TMStack.bodyCost_le (M.transition C.state (fun a => C.tape a (C.head a))).2.2 (List.finRange M.tapes)
  simp only [List.length_finRange] at ht
  dsimp [stepFactor]
  omega

 theorem run_exec (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) (v : ℕ)
    (hr : TMStack.Relative M C s) (hh : M.halted (M.step^[v] C)) :
    ∃u ≤ stepFactor M*v+1,∃s' ds',
      (runCode M).Exec (store M C.state s ds) u (store M (M.step^[v] C).state s' ds') ∧
      TMStack.Relative M (M.step^[v] C) s' ∧ ds'.length ≤ ds.length+v ∧
      (M.step^[v] C).head ⟨0,M.tapes_pos⟩ = C.head ⟨0,M.tapes_pos⟩+
        (ds'.map Move.displacement).sum-(ds.map Move.displacement).sum := by
  induction v generalizing C s ds with
  | zero =>
    refine ⟨1,by omega,s,ds,?_,hr,by simp,by simp⟩
    apply Code.Exec.loop_false
    simp only [live,select_store,decide_eq_false_iff_not,not_not]
    exact hh
  | succ v ih =>
    by_cases hhalt : M.halted C
    · have hf : M.step^[v+1] C=C := Function.iterate_fixed (by simp [TM.step,hhalt]) _
      refine ⟨1,by omega,s,ds,?_,by simpa only [hf] using hr,by simp,by simp [hf]⟩
      rw [hf]
      apply Code.Exec.loop_false
      simpa only [live,select_store,decide_eq_false_iff_not,not_not,TM.halted] using hhalt
    · let p := M.transition C.state (fun a => C.tape a (C.head a))
      have hC : (M.step C).state=p.1 := by simp only [TM.step,hhalt,ite_false,p]
      obtain ⟨a,ha,he⟩ := step_exec M C s ds hr
      change (step M).Exec _ a (store M p.1 (TMStack.nextTapes M p s) (p.2.2 ⟨0,M.tapes_pos⟩::ds)) at he
      obtain ⟨b,hb,s',ds',hf,hr',hlen,hhead⟩ := ih (M.step C) (TMStack.nextTapes M p s)
        (p.2.2 ⟨0,M.tapes_pos⟩::ds) (TMStack.next_relative M hr hhalt)
        (by simpa only [Function.iterate_succ_apply] using hh)
      rw [hC] at hf
      have ht : live M (tops (store M C.state s ds))=true := by
        simpa only [live,select_store,decide_eq_true_eq,TM.halted] using hhalt
      have hsf : 1 ≤ stepFactor M := by dsimp [stepFactor]; omega
      have ha' : a+1 ≤ stepFactor M := by omega
      refine ⟨a+b+1,by nlinarith, s',ds',?_,?_,?_,?_⟩
      · simpa only [Function.iterate_succ_apply,runCode] using Code.Exec.loop_true ht he hf
      · simpa only [Function.iterate_succ_apply] using hr'
      · simp only [List.length_cons] at hlen; omega
      · simp only [Function.iterate_succ_apply]
        rw [hhead]
        simp only [TM.step,hhalt,ite_false,List.map_cons,List.sum_cons,p]
        omega
end WLTime.TMTransducer

namespace WLTime.Move
 def inverse : Move → Move | .left => .right | .stay => .stay | .right => .left
 @[simp] theorem inverse_displacement (d : Move) : d.inverse.displacement= -d.displacement := by cases d <;> rfl
end WLTime.Move
namespace WLTime.TapePair
variable {A : Type uA}
def move (blank : A) (d : Move) (s : Tape A) : Tape A := moveWrite blank (s.right.headD blank) d s
 theorem contents_move (blank : A) (d : Move) (s : Tape A) (z : ℤ) :
    contents blank (move blank d s) z=contents blank s (z+d.displacement) := by
  rw [move,contents_moveWrite]
  split_ifs with h
  · rw [h,contents_zero]
  · rfl
end WLTime.TapePair
namespace WLTime.TMTransducer
open TypedStack
variable (M : TM)
def zeroTape : Fin M.tapes := ⟨0,M.tapes_pos⟩
def historyDecode : Option (Letter M) → Move
  | some (.inr (.inr d)) => d
  | _ => .stay
def rewindKey (v : Tops (Reg M) (Letter M)) : Move × Fin M.symbols :=
  (historyDecode M (v (historyReg M)),((v (.inr (zeroTape M,true))).map (symbolDecode M)).getD (TMStack.blank M))
def rewindBody (d : Move) (x : Fin M.symbols) : Code (Reg M) (Letter M) :=
  .seq (((TMStack.single (TMStack.blank M) (zeroTape M) x d.inverse).mapLetters Sum.inl (symbolDecode M)).relabel Sum.inr)
    (.pop (historyReg M))
noncomputable def rewindStep : Code (Reg M) (Letter M) :=
  .casesAll (rewindKey M) (fun x => rewindBody M x.1 x.2)
noncomputable def rewindCode : Code (Reg M) (Letter M) :=
  .loop (fun v => (v (historyReg M)).isSome) (rewindStep M)
def moveOrigin (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (d : Move) :=
  Function.update s (zeroTape M) (TapePair.move (TMStack.blank M) d.inverse (s (zeroTape M)))
def rewindTapes (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) : List Move → Fin M.tapes → TapePair.Tape (Fin M.symbols)
  | [] => s
  | d::ds => rewindTapes (moveOrigin M s d) ds

 theorem rewindBody_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (d : Move) (ds : List Move) :
    (rewindBody M d ((s (zeroTape M)).right.headD (TMStack.blank M))).Exec (store M q s (d::ds))
      (TMStack.tapeCost d.inverse+2) (store M q (moveOrigin M s d) ds) := by
  have he := TMStack.single_exec (TMStack.blank M) ((s (zeroTape M)).right.headD (TMStack.blank M))
    (zeroTape M) d.inverse s
  have hf := Code.mapLetters_exec (Sum.inl : Fin M.symbols → Letter M) (symbolDecode M) (by intro x; rfl) he
  have hg := Code.relabel_inr_exec hf
    (fun i : Fin 2 => if i.val=0 then [Sum.inr (Sum.inl q)] else (d::ds).map (fun d => Sum.inr (Sum.inr d)))
  let mid := store M q (moveOrigin M s d) (d::ds)
  have hp := Code.Exec.seq hg (Code.Exec.pop mid (historyReg M))
  unfold rewindBody
  convert hp using 1 <;> try rfl
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr k => rfl
noncomputable def rewindFactor : ℕ := 12+Fintype.card (Move × Fin M.symbols)
 theorem rewindStep_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (d : Move) (ds : List Move) :
    ∃u ≤ rewindFactor M-1,(rewindStep M).Exec (store M q s (d::ds)) u
      (store M q (moveOrigin M s d) ds) := by
  have hs : rewindKey M (tops (store M q s (d::ds)))=(d,(s (zeroTape M)).right.headD (TMStack.blank M)) := by
    apply Prod.ext
    · rfl
    · exact congrArg (fun v => (v (zeroTape M))) (congrArg Prod.snd (select_store M q s (d::ds)))
  have he := rewindBody_exec M q s d ds
  change ((fun x : Move × Fin M.symbols => rewindBody M x.1 x.2)
    (d,(s (zeroTape M)).right.headD (TMStack.blank M))).Exec _ _ _ at he
  rw [←hs] at he
  obtain ⟨u,hu,hf⟩ := Code.casesAll_exec (rewindKey M) (fun x => rewindBody M x.1 x.2) he
  refine ⟨u,?_,hf⟩
  have ht : TMStack.tapeCost d.inverse ≤ 8 := by cases d <;> decide
  dsimp [rewindFactor]
  omega
 theorem rewind_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) :
    ∃u ≤ rewindFactor M*ds.length+1,(rewindCode M).Exec (store M q s ds) u
      (store M q (rewindTapes M s ds) []) := by
  induction ds generalizing s with
  | nil => exact ⟨1,by simp,Code.Exec.loop_false rfl⟩
  | cons d ds ih =>
    obtain ⟨a,ha,he⟩ := rewindStep_exec M q s d ds
    obtain ⟨b,hb,hf⟩ := ih (moveOrigin M s d)
    have hp : 1 ≤ rewindFactor M := by dsimp [rewindFactor]; omega
    refine ⟨a+b+1,?_,Code.Exec.loop_true rfl he hf⟩
    simp only [List.length_cons]
    have hh : a+1 ≤ rewindFactor M := by omega
    nlinarith only [hh,hb]
 theorem rewind_contents (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) (z : ℤ) :
    TapePair.contents (TMStack.blank M) (rewindTapes M s ds (zeroTape M)) z=
      TapePair.contents (TMStack.blank M) (s (zeroTape M)) (z-(ds.map Move.displacement).sum) := by
  induction ds generalizing s z with
  | nil => simp only [rewindTapes,List.map_nil,List.sum_nil,sub_zero]
  | cons d ds ih =>
    rw [rewindTapes,ih]
    simp only [moveOrigin,Function.update_self,TapePair.contents_move,Move.inverse_displacement,
      List.map_cons,List.sum_cons]
    congr 1
    omega
 theorem rewind_absolute (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (hr : TMStack.Relative M C s) (hh : C.head (zeroTape M)=(ds.map Move.displacement).sum) (z : ℤ) :
    TapePair.contents (TMStack.blank M) (rewindTapes M s ds (zeroTape M)) z=C.tape (zeroTape M) z := by
  rw [rewind_contents,hr,hh]
  congr 1
  omega
end WLTime.TMTransducer

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]
def takeN (a b : K) (f : A → A) (zero : A) : ℕ → Code K A
  | 0 => .skip
  | n+1 => .seq (.seq (.pushDyn b (fun v => f ((v a).getD zero))) (.pop a)) (takeN a b f zero n)
def readN (zero : A) (xs : List A) (n : ℕ) : List A := List.ofFn (fun i : Fin n => xs.getD i.val zero)
 theorem takeN_exec (a b : K) (hab : a≠b) (f : A → A) (zero : A) (n : ℕ) (s : Stacks K A) :
    (takeN a b f zero n).Exec s (4*n+1)
      (Function.update (Function.update s a ((s a).drop n)) b
        (((readN zero (s a) n).map f).reverse++s b)) := by
  induction n generalizing s with
  | zero =>
    simpa only [takeN,readN,List.ofFn_zero,List.map_nil,List.reverse_nil,List.nil_append,List.drop_zero,
      Function.update_eq_self] using Exec.skip s
  | succ n ih =>
    let mid := Function.update (Function.update s b (f ((s a).headD zero)::s b)) a (s a).tail
    have hfirst : Exec (.seq (.pushDyn b (fun v => f ((v a).getD zero))) (.pop a)) s 4 mid := by
      have hp := Exec.pushDyn s b (fun v => f ((v a).getD zero))
      have he := Exec.seq hp (Exec.pop _ a)
      have hh : (s a).head?.getD zero=(s a).headD zero := by cases s a <;> rfl
      simpa only [mid,tops,hh,Function.update_of_ne hab] using he
    have he := Exec.seq hfirst (ih mid)
    have hread : readN zero (s a) (n+1)=(s a).headD zero::readN zero (s a).tail n := by
      unfold readN
      rw [List.ofFn_succ]
      apply congrArg₂ List.cons
      · cases s a <;> rfl
      · congr 1
        funext i
        exact (TapePair.getD_tail (s a) i.val zero).symm
    unfold takeN
    convert he using 1
    · omega
    · funext k
      by_cases hb : k=b
      · subst k
        simp [mid,hab.symm,hread,List.reverse_cons,List.append_assoc]
      · by_cases ha : k=a
        · subst k
          simp only [Function.update_self,Function.update_of_ne hb,mid]
          cases s a <;> simp
        · simp [mid,hb,ha]
 omit [DecidableEq K] in
 theorem takeN_size (a b : K) (f : A → A) (zero : A) (n : ℕ) :
    (takeN a b f zero n).controlSize=4*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [takeN,controlSize,ih]; omega
end WLTime.TypedStack.Code
namespace WLTime.TMTransducer
open TypedStack
variable (M : TM)
 theorem output_prefix (input output : List Bool) (ho : M.outputs input output)
    (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (hr : TMStack.Relative M (M.run input (M.time input)) s)
    (hh : (M.run input (M.time input)).head (zeroTape M)=(ds.map Move.displacement).sum) :
    Code.readN (TMStack.blank M) (rewindTapes M s ds (zeroTape M)).right output.length=output.map M.symbol := by
  apply List.ext_getElem
  · simp [Code.readN]
  · intro i hi hj
    have hit : i<output.length := by simpa [Code.readN] using hi
    have h := rewind_absolute M _ s ds hr hh (i : ℤ)
    have ho' := ho.2 ⟨i,hit⟩
    simpa only [Code.readN,List.getElem_ofFn,List.getElem_map,TapePair.contents,
      not_lt.mpr (Int.natCast_nonneg i),ite_false,Int.toNat_natCast,List.get_eq_getElem] using h.trans ho'
end WLTime.TMTransducer

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K] [Fintype K]
def mass (s : Stacks K A) : ℕ := ∑ k, (s k).length
 theorem mass_update (s : Stacks K A) (k : K) (xs : List A) :
    mass (Function.update s k xs)+(s k).length=mass s+xs.length := by
  unfold mass
  have he : (fun j => (Function.update s k xs j).length)=Function.update (fun j => (s j).length) k xs.length := by
    funext j
    by_cases h : j=k <;> simp [h]
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ k),Finset.sdiff_singleton_eq_erase]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  omega
 theorem mass_exec {c : Code K A} {s : Stacks K A} {t : ℕ} {out : Stacks K A} (h : c.Exec s t out) :
    mass out≤ mass s+t := by
  induction h with
  | skip => omega
  | push s k x => have h := mass_update s k (x::s k); simp only [List.length_cons] at h; omega
  | pushDyn s k f => have h := mass_update s k (f (tops s)::s k); simp only [List.length_cons] at h; omega
  | pop s k => have h := mass_update s k (s k).tail; simp only [List.length_tail] at h; omega
  | seq _ _ ih ih' => omega
  | branch_true _ _ ih => omega
  | branch_false _ _ ih => omega
  | loop_false => omega
  | loop_true _ _ _ ih ih' => omega

def clearList : List K → Code K A
  | [] => .skip
  | k::ks => .seq (.clear k) (clearList ks)
def cleared (ks : List K) (s : Stacks K A) : Stacks K A := fun k => if k ∈ ks then [] else s k
 omit [Fintype K] in
 theorem clearList_exec (ks : List K) (s : Stacks K A) (hk : ks.Nodup) :
    (clearList ks).Exec s (3*(ks.map (fun k => (s k).length)).sum+ks.length+1) (cleared ks s) := by
  induction ks generalizing s with
  | nil =>
    have hz : cleared ([] : List K) s=s := by funext k; simp [cleared]
    rw [hz]
    simpa [clearList] using Exec.skip s
  | cons k ks ih =>
    obtain ⟨hn,hd⟩ := List.nodup_cons.mp hk
    have he := Exec.seq (clear_exec k s) (ih (Function.update s k []) hd)
    have hsum : (ks.map (fun j => (Function.update s k [] j).length)).sum=(ks.map (fun j => (s j).length)).sum := by
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [Function.update_of_ne (by intro h; subst j; exact hn hj)]
    have hout : cleared ks (Function.update s k [])=cleared (k::ks) s := by
      funext j
      by_cases h : j=k <;> by_cases hh : j∈ks <;> simp [cleared,h,hh]
    rw [hsum,hout] at he
    convert he using 1 <;> try rfl
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega
 theorem clearList_cost (ks : List K) (s : Stacks K A) (hk : ks.Nodup) :
    (ks.map (fun k => (s k).length)).sum≤ mass s := by
  rw [←List.sum_toFinset _ hk]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
end WLTime.TypedStack.Code

end OAI
