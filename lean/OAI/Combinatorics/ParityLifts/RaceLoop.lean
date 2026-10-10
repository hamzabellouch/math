import OAI.Combinatorics.ParityLifts.RaceStage

namespace OAI

namespace ParityWL.Complexity

abbrev RaceState := Bool × (Bool × (ℕ × List Bool))

def raceStep (M : Machine) (x : RaceState) : RaceState :=
  let a := raceStage M x.2.2.1 x.2.2.2
  (!a.1,(a.2,(x.2.2.1+1,x.2.2.2)))

noncomputable def PolyProgram.raceStep (M : Machine) : PolyProgram RaceState RaceState (Complexity.raceStep M) := by
  let core : PolyProgram RaceState (ℕ × List Bool) (fun x => x.2.2) :=
    .expr TExpr.input.right.right (by intro x; rfl)
  let stage := core.comp (PolyProgram.raceStage M)
  let flag := (stage.comp (PolyProgram.fst Bool Bool)).comp PolyProgram.not
  let ans := stage.comp (PolyProgram.snd Bool Bool)
  let next := ((core.comp (PolyProgram.fst ℕ (List Bool))).comp PolyProgram.natSucc).pair
    (core.comp (PolyProgram.snd ℕ (List Bool)))
  exact flag.pair (ans.pair next)

lemma raceState_size (a b : Bool) (n : ℕ) (bs : List Bool) :
    (treeEncode (a,(b,(n,bs)))).size ≤ 20*(n+bs.length+1) := by
  have ha := bool_size a
  have hb := bool_size b
  have hs := treeEncode_bits_size bs
  simp only [treeEncode_pair,DataTree.size,treeEncode_nat,numTree_size]
  omega

noncomputable def raceStepBudget (M : Machine) (B L : ℕ) : ℕ :=
  (PolyProgram.raceStep M).coefficient*(20*(B+L+2)+1)^(PolyProgram.raceStep M).degree

lemma raceStepBudget_bound (M : Machine) (bs : List Bool) (B n : ℕ) (b : Bool) (hn : n ≤ B+1) :
    (PolyProgram.raceStep M).program.time (true,(b,(n,bs))) ≤ raceStepBudget M B bs.length := by
  apply (PolyProgram.raceStep M).bound _ |>.trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have h := raceState_size true b n bs
  omega

lemma raceLoop_run (M : Machine) (bs : List Bool) (P : Bool → Prop)
    (hM : ∀ j : ℕ, 0<j → ∀ k : ℕ, 4 ≤ k → ∃ s b, Emits M (trialInput j k bs) s b ∧ P b)
    (B : ℕ) (hB : (raceStage M B bs).1=true) :
    ∀ fuel n : ℕ, n+fuel=B → ∀ a : Bool, ∃ m b, m ≤ B+1 ∧
      BEval (.loop (PolyProgram.raceStep M).program.code) (treeEncode (true,(a,(n,bs))))
        ((fuel+2)*(raceStepBudget M B bs.length+20*(B+bs.length+2)+1))
        (treeEncode (false,(b,(m,bs)))) ∧ P b := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn a
    have hn' : n=B := by omega
    subst n
    let ans := (raceStage M B bs).2
    have hstep := ((PolyProgram.raceStep M).program.run (true,(a,(B,bs)))).mono
      (raceStepBudget_bound M bs B B a (by omega))
    have he : raceStep M (true,(a,(B,bs)))=(false,(ans,(B+1,bs))) := by
      simp only [raceStep,hB,Bool.not_true,ans]
    rw [he] at hstep
    have hs := raceState_size false ans (B+1) bs
    have hstop := BEval.loop_stop (PolyProgram.raceStep M).program.code
      (treeEncode (false,(ans,(B+1,bs)))) rfl
    refine ⟨B+1,ans,le_rfl,?_,raceStage_sound M bs P hM B hB⟩
    apply (BEval.loop_next (by simp [DataTree.child]) hstep hstop).mono
    omega
  | succ fuel ih =>
    intro n hn a
    let ans := (raceStage M n bs).2
    have hstep := ((PolyProgram.raceStep M).program.run (true,(a,(n,bs)))).mono
      (raceStepBudget_bound M bs B n a (by omega))
    cases hh : (raceStage M n bs).1 with
    | true =>
      have he : raceStep M (true,(a,(n,bs)))=(false,(ans,(n+1,bs))) := by
        simp only [raceStep,hh,Bool.not_true,ans]
      rw [he] at hstep
      have hs := (raceState_size false ans (n+1) bs).trans
        (show 20*(n+1+bs.length+1) ≤ 20*(B+bs.length+2) by omega)
      have hstop := BEval.loop_stop (PolyProgram.raceStep M).program.code
        (treeEncode (false,(ans,(n+1,bs)))) rfl
      refine ⟨n+1,ans,by omega,?_,raceStage_sound M bs P hM n hh⟩
      apply (BEval.loop_next (by simp [DataTree.child]) hstep hstop).mono
      nlinarith
    | false =>
      have he : raceStep M (true,(a,(n,bs)))=(true,(ans,(n+1,bs))) := by
        simp only [raceStep,hh,Bool.not_false,ans]
      rw [he] at hstep
      obtain ⟨m,b,hm,hr,hP⟩ := ih (n+1) (by omega) ans
      refine ⟨m,b,hm,?_,hP⟩
      apply (BEval.loop_next (by simp [DataTree.child]) hstep hr).mono
      nlinarith

def raceInitExpr : TExpr := .pair (.const (treeEncode true)) (.pair .nil (.pair .nil .input))

noncomputable def raceCode (M : Machine) : FCode :=
  .seq raceInitExpr.compile (.seq (.loop (PolyProgram.raceStep M).program.code) (.seq .right .left))

lemma raceCode_run (M : Machine) (bs : List Bool) (P : Bool → Prop)
    (hM : ∀ j : ℕ, 0<j → ∀ k : ℕ, 4 ≤ k → ∃ s b, Emits M (trialInput j k bs) s b ∧ P b)
    (B : ℕ) (hB : (raceStage M B bs).1=true) :
    ∃ b,BEval (raceCode M) (treeEncode bs)
      (1000*(B+bs.length+2)^2*(raceStepBudget M B bs.length+1)) (treeEncode b) ∧ P b := by
  obtain ⟨m,b,hm,hr,hP⟩ := raceLoop_run M bs P hM B hB B 0 (by omega) false
  have hi : BEval raceInitExpr.compile (treeEncode bs) (raceInitExpr.cost*((treeEncode bs).size+1))
      (treeEncode (true,(false,(0,bs)))) := raceInitExpr.run _
  have ho := (BEval.right (treeEncode (false,(b,(m,bs))))).seq (BEval.left (treeEncode (b,(m,bs))))
  change BEval _ _ _ (treeEncode b) at ho
  refine ⟨b,(hi.seq (hr.seq ho)).mono ?_,hP⟩
  have hs := (raceState_size false b m bs).trans (show 20*(m+bs.length+1) ≤ 20*(B+bs.length+2) by omega)
  have hbits := treeEncode_bits_size bs
  have hp : (treeEncode (b,(m,bs))).size ≤ (treeEncode (false,(b,(m,bs)))).size := by
    simp only [treeEncode_pair,treeEncode_false,DataTree.size]; omega
  simp only [raceInitExpr,TExpr.cost,treeEncode_true,DataTree.size]
  let X := B+bs.length+2
  have hX : 2 ≤ X := by dsimp [X]; omega
  have hB' : B+2 ≤ X := by dsimp [X]; omega
  have hL : (treeEncode bs).size+1 ≤ 4*X := by dsimp [X]; omega
  have hloop := Nat.mul_le_mul_right (raceStepBudget M B bs.length+20*X+1) hB'
  change _ ≤ 1000*X^2*(raceStepBudget M B bs.length+1)
  change _ ≤ 20*X at hs
  have hprod := Nat.mul_le_mul_right (raceStepBudget M B bs.length) (show X ≤ X^2 by nlinarith only [hX])
  generalize hR : raceStepBudget M B bs.length = R at hloop hprod ⊢
  change 9*((treeEncode bs).size+1)+((B+2)*(R+20*X+1)+_+1)+1 ≤ _
  nlinarith only [hX,hB',hL,hloop,hs,hp,hprod]

end ParityWL.Complexity

end OAI
