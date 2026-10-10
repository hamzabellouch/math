import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineScheduleNat
import OAI.Combinatorics.MatchingCount.Tapes.Codec

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

def numStep (x : Symbol×List ℕ) : List ℕ :=
  if x.1=3 then 0::x.2
  else if x.1=1 then (2*x.2.headD 0)::x.2.tail
  else if x.1=2 then (2*x.2.headD 0+1)::x.2.tail
  else x.2

def eqSymbol (a : Symbol) : Realizer (fun b : Symbol=>decide (b=a)) :=
  (composition (pair valRealizer (constant a.val)) natEqual).congr
    (fun b=>by simp only [Function.comp_apply,Fin.ext_iff])
lemma polynomial_eqSymbol (a : Symbol) : PolynomialTime (eqSymbol a) := by
  unfold eqSymbol; apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_val (polynomial_constant _)) polynomial_natEqual

def numStepRealizer : Realizer numStep :=
  (choose (composition first (eqSymbol 3))
    (composition (pair (constant 0) second) listCons)
    (choose (composition first (eqSymbol 1))
      (composition (pair ((constant 2).mulNat (composition second (head 0))) (composition second tail)) listCons)
      (choose (composition first (eqSymbol 2))
        (composition (pair (((constant 2).mulNat (composition second (head 0))).addNat (constant 1)) (composition second tail)) listCons)
        second))).congr (fun x=>by simp only [Function.comp_apply,decide_eq_true_eq,numStep])
lemma polynomial_numStep : PolynomialTime numStepRealizer := by
  unfold numStepRealizer
  apply polynomial_congr
  have := polynomial_eqSymbol 3
  have := polynomial_eqSymbol 2
  have := polynomial_eqSymbol 1
  have := polynomial_head (0:ℕ)
  have := polynomial_tail (A:=ℕ)
  simp only [Realizer.mulNat, Realizer.addNat]
  tree_cost

lemma weight_double (n : ℕ) : weight (2*n)≤weight n+2 := by
  by_cases hn:n=0
  · subst n; simp only [Nat.mul_zero]; omega
  rw [weight_nat,Nat.bit0_bits n hn]
  rw [weight_cons]
  change 1+1+weight n≤_
  omega
lemma weight_double_one (n : ℕ) : weight (2*n+1)≤weight n+4 := by
  rw [weight_nat,Nat.bit1_bits,weight_cons]
  change 1+3+weight n≤_
  omega

lemma numStep_weight (a : Symbol) (ns : List ℕ) : weight (numStep (a,ns))≤weight ns+6 := by
  unfold numStep
  dsimp only
  split_ifs
  · rw [weight_cons]; change 1+1+weight ns≤_; omega
  · cases ns with
    | nil => change 3≤1+6; omega
    | cons n ns =>
      simp only [List.headD_cons,List.tail_cons,weight_cons]
      have h:=weight_double n
      omega
  · cases ns with
    | nil => change 7≤7; omega
    | cons n ns =>
      simp only [List.headD_cons,List.tail_cons,weight_cons]
      have h:=weight_double_one n
      omega
  · omega

lemma fold_weight (as : List Symbol) (ns : List ℕ) :
    weight (as.foldl (fun ns a=>numStep (a,ns)) ns)≤weight ns+6*as.length := by
  induction as generalizing ns with
  | nil => simp
  | cons a as ih =>
    have h:=ih (numStep (a,ns))
    have h':=numStep_weight a ns
    simp only [List.foldl_cons,List.length_cons]
    omega
lemma polynomial_numFold : PolynomialTime (fold numStepRealizer) := by
  apply polynomial_fold polynomial_numStep (7*X)
  intro as ns pre post he
  have h:=fold_weight pre ns
  have hlen : pre.length≤as.length := by rw [he,List.length_append]; omega
  have hlen':=list_length_le_weight as
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

def parse (as : List Symbol) : List ℕ := as.foldr (fun a ns=>numStep (a,ns)) []
def parseRealizer : Realizer parse :=
  (composition (pair reverse (constant [])) (fold numStepRealizer)).congr (fun as=>by
    simp only [Function.comp_apply,List.foldl_reverse,parse])
lemma polynomial_parse : PolynomialTime parseRealizer := by
  unfold parseRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant _)) polynomial_numFold

lemma bits_fold (n : ℕ) (ns : List ℕ) :
    (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=n::ns := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn,List.map_cons,List.foldr_cons,ih]
    cases b <;> simp [fromBit,numStep,Nat.bit]
lemma encodeNat_fold (n : ℕ) (ns : List ℕ) :
    (encodeNat n).foldr (fun a ns=>numStep (a,ns)) ns=n::ns := by
  change (n.bits.map fromBit++[3]).foldr _ ns=_
  rw [List.foldr_append]
  change (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=_
  exact bits_fold n ns
lemma encodeInt_fold (z : ℤ) (ns : List ℕ) :
    (encodeInt z).foldr (fun a ns=>numStep (a,ns)) ns=z.natAbs::ns := by
  unfold encodeInt
  rw [List.foldr_append,encodeNat_fold]
  split_ifs <;> simp [numStep]
lemma encodeRat_fold (q : ℚ) (ns : List ℕ) :
    (encodeRat q).foldr (fun a ns=>numStep (a,ns)) ns=q.num.natAbs::q.den::ns := by
  rw [encodeRat,List.foldr_append,encodeNat_fold,encodeInt_fold]
end MatchingFPRAS.LiteralParse

end OAI
