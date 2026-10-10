import OAI.Computability.RandomMean.InputBounds

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
abbrev Acc := Env×State
noncomputable def advance : Code (Acc×Count) Acc :=
  (fst ≫ₚ fst) ⋏ₚ (((fst ≫ₚ fst) ⋏ₚ snd ⋏ₚ (fst ≫ₚ snd)) ≫ₚ dispatch)
@[simp] theorem advance_eval (e : Env) (s : State) (c : Count) : advance ((e,s),c)=(e,dispatch (e,c,s)) := rfl
 theorem fold_estimates (e : Env) (cs : List Count) {n H E D T : ℕ}
    (hs : e.2.2.1.length ≤ H) (hj : e.2.2.2.1.length ≤ H)
    (he : RawBasic.ArenaBounded e.1 E) (hd : e.2.2.2.2.length*(E+1)+20 ≤ D) (hT : 22 ≤ T)
    (s : State) (M : ℕ) (hc : StateSmall n H M s) (ht : StateTags T s) :
    (Fold.fold advance.eval (e,s) cs).1=e ∧
    StateSmall n H (M+cs.length*D) (Fold.fold advance.eval (e,s) cs).2 ∧
    stateMass (Fold.fold advance.eval (e,s) cs).2  ≤  stateMass s+3*cs.length ∧
    (Fold.fold advance.eval (e,s) cs).2.2.length ≤ s.2.length+2*cs.length ∧
    StateTags T (Fold.fold advance.eval (e,s) cs).2 := by
  induction cs generalizing s M with
  | nil => simpa [Fold.fold] using And.intro (rfl : e=e) (And.intro hc (And.intro (le_refl (stateMass s)) (And.intro (le_refl s.2.length) ht)))
  | cons c cs ih =>
    have hc' : StateSmall n H (M+D) (dispatch (e,c,s)) := dispatch_small hc.1 hc.2 hs hj he hd
    have ht' : StateTags T (dispatch (e,c,s)) := dispatch_tags hT ht
    have hm := dispatch_mass (e,c,s)
    have hh := ih (dispatch (e,c,s)) (M+D) hc' ht'
    rw [show Fold.fold advance.eval (e,s) (c::cs)=Fold.fold advance.eval (e,dispatch (e,c,s)) cs by rfl, List.length_cons]
    refine ⟨hh.1,?_,?_,?_,hh.2.2.2.2⟩
    · convert hh.2.1 using 1 ; ring
    · change stateMass (dispatch (e,c,s)) ≤  stateMass s+3 ∧ _ at hm
      omega
    · change _ ∧ (dispatch (e,c,s)).2.length ≤ s.2.length+2 at hm
      omega
 theorem prefix_size (s : Acc) (cs : List Count) (k : ℕ) (hk : k ≤ cs.length) :
    treeSize (encode (Fold.fold advance.eval s (cs.take k))) ≤
      1099511627776*(treeSize (encode (s,cs))+1)^12 := by
  let N := treeSize (encode (s,cs))+1
  have hs : treeSize (encode s) ≤ N := (Size.fst (s,cs)).trans (Nat.le_succ _)
  have he : treeSize (encode s.1) ≤ N := (Size.fst s).trans hs
  have hz : treeSize (encode s.2) ≤ N := (Size.snd s).trans hs
  have hg : treeSize (encode s.1.1) ≤ N := (Size.fst s.1).trans he
  have he2 := (Size.snd s.1).trans he
  have he22 := (Size.snd s.1.2).trans he2
  have he222 := (Size.snd s.1.2.2).trans he22
  have hsamp : s.1.2.2.1.length ≤ N := (Size.length _).trans ((Size.fst _).trans he22)
  have htrial : s.1.2.2.2.1.length ≤ N := (Size.length _).trans ((Size.fst _).trans he222)
  have hbasic : s.1.2.2.2.2.length ≤ N := (Size.length _).trans ((Size.snd _).trans he222)
  have hn : 1 ≤ N := Nat.le_add_left _ _
  have n2 : N ≤ N^2 := Nat.le_pow (by decide)
  have n3 : N^2 ≤ N^3 := Nat.pow_le_pow_right hn (by omega)
  have n12 : N^3 ≤ N^12 := Nat.pow_le_pow_right hn (by omega)
  have hl : (cs.take k).length ≤ N :=
    (List.length_take_le _ _).trans (hk.trans ((Size.length cs).trans ((Size.snd (s,cs)).trans (Nat.le_succ _))))
  let D := N*(N+1)+20
  have hh := fold_estimates s.1 (cs.take k) hsamp htrial
    (fun v hv e he => (RawBasic.arenaBounded_size _ v hv e he).trans hg)
    (show s.1.2.2.2.2.length*(N+1)+20 ≤ D by dsimp [D]; gcongr)
    (show 22 ≤ N+22 by omega) s.2 N (stateSmall_of_size hz) ((stateTags_of_size hz).mono (by omega))
  simp only [Prod.eta] at hh
  let U := 50*N^3
  have hu : 1 ≤ U := by dsimp [U]; omega
  have hnu : N ≤ U := by dsimp [U]; omega
  have hMu : N+(cs.take k).length*D ≤ U := by
    have hmul := Nat.mul_le_mul_right D hl
    dsimp [D] at hmul ⊢
    dsimp [U]
    nlinarith
  have hmass : stateMass (Fold.fold advance.eval s (cs.take k)).2 ≤ U := by
    have h0 := stateMass_size s.2
    dsimp [U]
    have h1 := hh.2.2.1
    omega
  have hdepth : (Fold.fold advance.eval s (cs.take k)).2.2.length ≤ U := by
    have h0 := (Size.length s.2.2).trans ((Size.snd s.2).trans hz)
    have h1 := hh.2.2.2.1
    dsimp [U]; omega
  have htag : StateTags U (Fold.fold advance.eval s (cs.take k)).2 := hh.2.2.2.2.mono (by dsimp [U]; omega)
  have hout := state_small_size hh.2.1 htag hu hnu hnu hMu hmass hdepth
  rw [←Prod.eta (Fold.fold advance.eval s (cs.take k)),Size.pair]
  rw [hh.1]
  change _ ≤ 1099511627776*N^12
  dsimp [U] at hout
  rw [mul_pow,←pow_mul] at hout
  norm_num at hout
  nlinarith
noncomputable def loop : Code (Acc×List Count) Acc := foldPrefix advance 1099511627776 12 prefix_size
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.RandomTree
@[simp] theorem all_const_iff {α : Type} (t : RandomTree α) (P : Prop) : t.All (fun _ => P) ↔ P := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp only [All,hl,hr,and_self]
end MeanPayoff.RandomTree
namespace MeanPayoff.SourceControl

theorem sampledResume_all {G : Game} {B : ℕ} {A C R : Result G B} (f : Frame G B A C)
    (v : A.Value) (k : Kont G B C R) (Q : State G B R→Prop) :
    (resume f v k).tree.All (fun p => Q p.1) ↔
      (RandomTree.uniformBelow (sampleExponent B)).All (fun j => Q (sampledResume f v k j)) := by
  cases f
  all_goals simp only [resume,sampledResume]
  all_goals try split_ifs
  all_goals simp [Counted.pure,Counted.map,Counted.lift,RandomTree.all_map,RandomTree.All]

theorem sampledResume_expect {G : Game} {B : ℕ} {A C R : Result G B} (f : Frame G B A C)
    (v : A.Value) (k : Kont G B C R) (Q : State G B R→ℚ) :
    (resume f v k).tree.expect (fun p => Q p.1) =
      (RandomTree.uniformBelow (sampleExponent B)).expect (fun j => Q (sampledResume f v k j)) := by
  cases f
  all_goals simp only [resume,sampledResume]
  all_goals try split_ifs
  all_goals simp [Counted.pure,Counted.map,Counted.lift,RandomTree.expect_map,Function.comp_def]

theorem sampledStep_all {G : Game} {B : ℕ} {R : Result G B} (s : State G B R) (Q : State G B R→Prop) :
    (step s).tree.All (fun p => Q p.1) ↔
      (RandomTree.uniformBelow (sampleExponent B)).All (fun j => Q (sampledStep j s)) := by
  cases s with
  | ret k v =>
    cases k with
    | done => simp [step,sampledStep,Counted.pure,RandomTree.All]
    | push f k => exact sampledResume_all f v k Q
  | call j k =>
    cases j
    all_goals simp only [step,sampledStep]
    all_goals try split_ifs
    all_goals try simp [Counted.charge,Counted.pure,RandomTree.all_map,RandomTree.All]
    all_goals split <;> simp_all [RandomTree.All]

theorem sampledStep_expect {G : Game} {B : ℕ} {R : Result G B} (s : State G B R) (Q : State G B R→ℚ) :
    (step s).tree.expect (fun p => Q p.1) =
      (RandomTree.uniformBelow (sampleExponent B)).expect (fun j => Q (sampledStep j s)) := by
  cases s with
  | ret k v =>
    cases k with
    | done => simp [step,sampledStep,Counted.pure]
    | push f k => exact sampledResume_expect f v k Q
  | call j k =>
    cases j
    all_goals simp only [step,sampledStep]
    all_goals try split_ifs
    all_goals try simp [Counted.charge,Counted.pure,RandomTree.expect_map]
    all_goals split <;> simp_all

end MeanPayoff.SourceControl

end

section
namespace MeanPayoff.SourceControl

def sampledRun {G : Game} {B : ℕ} {R : Result G B} : ℕ → State G B R → RandomTree (State G B R)
  | 0,s => .leaf s
  | n+1,s => (RandomTree.uniformBelow (sampleExponent B)).bind fun j => sampledRun n (sampledStep j s)

theorem sampledRun_all {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R) (Q : State G B R→Prop) :
    (sampledRun n s).All Q ↔ (run n s).tree.All (fun p => Q p.1) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [sampledRun,RandomTree.all_bind,run,Counted.bind,RandomTree.all_bind,RandomTree.all_map]
    simp_rw [ih]
    exact (sampledStep_all s (fun t => (run n t).tree.All (fun p => Q p.1))).symm

theorem sampledRun_expect {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R) (Q : State G B R→ℚ) :
    (sampledRun n s).expect Q = (run n s).tree.expect (fun p => Q p.1) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [sampledRun,RandomTree.expect_bind,run,Counted.bind,RandomTree.expect_bind,RandomTree.expect_map]
    simp_rw [ih]
    exact (sampledStep_expect s (fun t => (run n t).tree.expect (fun p => Q p.1))).symm
end MeanPayoff.SourceControl
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

def drawSamples (e n : ℕ) : RandomTree (List Count) :=
  match n with
  | 0 => .leaf []
  | n+1 => (RandomTree.uniformBelow e).bind fun j => (drawSamples e n).map (List.replicate j () :: ·)

theorem samples_length (e n : ℕ) : (drawSamples e n).All (fun cs => cs.length=n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [drawSamples,RandomTree.all_bind,RandomTree.all_map]
    apply RandomTree.all_of_forall
    intro j
    exact RandomTree.all_mono _ ih (by intro cs h; simpa using h)

theorem loop_rep {G : Game} {B : ℕ} {R : SourceControl.Result G B}
    (s : SourceControl.State G B R) (z : State) (h : StateRep s z)
    (e : Env) (he : EnvRep G B e) (cs : List Count) :
    StateRep (cs.foldl (fun s c => SourceControl.sampledStep c.length s) s) (loop ((e,z),cs)).2 := by
  change StateRep _ (Fold.fold advance.eval (e,z) cs).2
  induction cs generalizing s z with
  | nil => exact h
  | cons c cs ih =>
    exact ih _ _ (sampled_dispatch_rep h e he c)

theorem samples_fold_expect {G : Game} {B : ℕ} {R : SourceControl.Result G B}
    (n : ℕ) (s : SourceControl.State G B R) (Q : SourceControl.State G B R→ℚ) :
    (drawSamples (sampleExponent B) n).expect (fun cs => Q (cs.foldl (fun s c => SourceControl.sampledStep c.length s) s)) =
      (SourceControl.sampledRun n s).expect Q := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [drawSamples,RandomTree.expect_bind,RandomTree.expect_map,Function.comp_def,List.foldl_cons,List.length_replicate,
      SourceControl.sampledRun]
    simp_rw [ih]

theorem samples_fold_all {G : Game} {B : ℕ} {R : SourceControl.Result G B}
    (n : ℕ) (s : SourceControl.State G B R) (Q : SourceControl.State G B R→Prop) :
    (drawSamples (sampleExponent B) n).All (fun cs => Q (cs.foldl (fun s c => SourceControl.sampledStep c.length s) s)) ↔
      (SourceControl.sampledRun n s).All Q := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [drawSamples,RandomTree.all_bind,RandomTree.all_map,List.foldl_cons,List.length_replicate,
      SourceControl.sampledRun]
    simp_rw [ih]
end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
