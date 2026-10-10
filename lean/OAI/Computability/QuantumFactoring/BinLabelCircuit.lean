import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionPredicates
import OAI.Computability.QuantumFactoring.ContinuedFractionCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- Input order Q,B,k,d,j; coprimality is already guaranteed by the convergent
recurrence and does not require a second gcd computation. -/
def binCheckExpr : NatExpr (Fin 5) :=
  let Q := NatExpr.var 0
  let B := NatExpr.var 1
  let k := NatExpr.var 2
  let d := NatExpr.var 3
  let j := NatExpr.var 4
  let bin := NatExpr.div (.add (.mul (.mul (.const 2) j) Q) d) (.mul (.const 2) d)
  .iteLe (.const 1) d
    (.iteLe (.add d (.const 1)) B
      (.iteLe (.add j (.const 1)) d
        (.testEq bin k (.const 1) (.const 0)) (.const 0)) (.const 0)) (.const 0)

lemma binCheckExpr_eval (x : Fin 5 → ℕ) :
    binCheckExpr.eval x=1 ↔ 0<x 3 ∧ x 3<x 1 ∧ x 4<x 3 ∧ bin (x 0) (x 3) (x 4)=x 2 := by
  unfold bin
  by_cases hd : 1≤x 3 <;> by_cases hB : x 3+1≤x 1 <;>
    by_cases hj : x 4+1≤x 3 <;>
    by_cases he : (2*x 4*x 0+x 3)/(2*x 3)=x 2 <;>
    simp [binCheckExpr,NatExpr.eval_testEq,NatExpr.eval,hd,hB,hj,he] <;> omega

def checkedConvergent {n w : ℕ} (i : ℕ) (Q B k : BooleanNetwork n w) : BooleanNetwork n (w+w) :=
  let conv := (k.pair Q).comp (convergentNet w i)
  let d := conv.comp (rootGuess w)
  let j := conv.comp (rootModulus w)
  let pass := binCheckExpr.isOne ![Q,B,k,d,j]
  (wordMux pass d (wordConstant (BitVec.ofNat w 0))).pair
    (wordMux pass j (wordConstant (BitVec.ofNat w 0)))

def checkedPair (Q B k i : ℕ) : ℕ×ℕ :=
  let p := convergentPair k Q i
  if IsBinLabel Q B k (p.2,p.1) then (p.2,p.1) else (0,0)

lemma checkedConvergent_value {n s w : ℕ} (i : ℕ) (hw : cfWidth s i ≤ w)
    (Q B k : BooleanNetwork n w) (x : Basis n)
    (hQ : (bitsValue (Q.eval x)).toNat<2^s) (hk : (bitsValue (k.eval x)).toNat<2^s) :
    ∃ d j : Basis w,
      (checkedConvergent i Q B k).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=checkedPair
        (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat i := by
  obtain ⟨p,q,hpq,he⟩ := convergentNet_value i hw (k.eval x) (Q.eval x) hk hQ
  let cv := (k.pair Q).comp (convergentNet w i)
  have hv : cv.eval x=Fin.append p q := by rw [eval_comp,eval_pair,hpq]
  let den := cv.comp (rootGuess w)
  let num := cv.comp (rootModulus w)
  have hd : den.eval x=q := by rw [eval_comp,hv,rootGuess_eval]
  have hj : num.eval x=p := by rw [eval_comp,hv,rootModulus_eval]
  let pass := binCheckExpr.isOne ![Q,B,k,den,num]
  have hc : pass.eval x 0=true ↔ IsBinLabel (bitsValue (Q.eval x)).toNat
      (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat
      ((bitsValue q).toNat,(bitsValue p).toNat) := by
    rw [NatExpr.isOne_eval,binCheckExpr_eval]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Matrix.cons_val_succ,hd,hj]
    have hr := convergentPair_reduced (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i
    have hpv : (bitsValue p).toNat = (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).1 := congrArg Prod.fst he
    have hqv : (bitsValue q).toNat = (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).2 := congrArg Prod.snd he
    change 0<(bitsValue q).toNat ∧ (bitsValue q).toNat<(bitsValue (B.eval x)).toNat ∧
      (bitsValue p).toNat<(bitsValue q).toNat ∧
      bin (bitsValue (Q.eval x)).toNat (bitsValue q).toNat (bitsValue p).toNat=(bitsValue (k.eval x)).toNat ↔ _
    have hcop : Nat.Coprime (bitsValue p).toNat (bitsValue q).toNat := by
      rw [hpv,hqv]
      exact hr.2
    exact ⟨fun ⟨a,b,c,e⟩ => ⟨a,b,c,hcop,e⟩,fun ⟨a,b,c,_,e⟩ => ⟨a,b,c,e⟩⟩
  have he' : ((bitsValue q).toNat,(bitsValue p).toNat)=
      ((convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).2,
        (convergentPair (bitsValue (k.eval x)).toNat (bitsValue (Q.eval x)).toNat i).1) :=
    congrArg Prod.swap he
  let zero := (wordConstant (n:=n) (BitVec.ofNat w 0)).eval x
  have hz : (bitsValue zero).toNat=0 := by simp [zero,wordConstant_eval]
  by_cases hh : IsBinLabel (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat
      (bitsValue (k.eval x)).toNat ((bitsValue q).toNat,(bitsValue p).toNat)
  · refine ⟨q,p,?_,?_⟩
    · rw [checkedConvergent,eval_pair]
      change Fin.append ((wordMux pass den _).eval x) ((wordMux pass num _).eval x)=_
      rw [wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hh),ite_eq_left (hc.mpr hh),hd,hj]
    · rw [checkedPair,← he',ite_eq_left hh]
  · refine ⟨zero,zero,?_,?_⟩
    · rw [checkedConvergent,eval_pair]
      change Fin.append ((wordMux pass den _).eval x) ((wordMux pass num _).eval x)=_
      rw [wordMux_eval,wordMux_eval,ite_eq_right (fun h => hh (hc.mp h)),ite_eq_right (fun h => hh (hc.mp h))]
    · rw [checkedPair,← he',ite_eq_right hh,hz]

lemma checkedPair_nonzero_iff {Q B k i : ℕ} :
    (checkedPair Q B k i).1≠0 ↔
      IsBinLabel Q B k ((convergentPair k Q i).2,(convergentPair k Q i).1) := by
  dsimp only [checkedPair]
  split_ifs with h
  · exact ⟨fun _ => h,fun _ => Nat.ne_of_gt h.1⟩
  · simp [h]
lemma checkedPair_sound {Q B k i : ℕ} (h : (checkedPair Q B k i).1≠0) :
    IsBinLabel Q B k (checkedPair Q B k i) := by
  have hh := checkedPair_nonzero_iff.mp h
  simp [checkedPair,hh]

end ExactQuantumFactoring.OrderTrial


end

end OAI
