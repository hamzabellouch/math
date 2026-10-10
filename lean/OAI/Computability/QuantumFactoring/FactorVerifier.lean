import Mathlib
import OAI.Computability.QuantumFactoring.AKSBounds
import OAI.Computability.QuantumFactoring.WordResize
import OAI.Computability.QuantumFactoring.FactorEncoding

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

lemma rootWidth_ge (n : ℕ) : n≤rootWidth n := by
  dsimp [rootWidth]
  nlinarith

/-- The range check makes the AKS interface exact also for the invalid 0,1
entries occurring in arbitrary uniform guesses. -/
def primeWord (n : ℕ) : BooleanNetwork n 1 :=
  (wordLe (wordConstant (BitVec.ofNat n 2)) (select id)).band
    ((resizeWord n (rootWidth n)).comp (primalityNet n))

lemma primeWord_value {n : ℕ} (hn : 128≤n) (x : Basis n) :
    (primeWord n).eval x 0=true ↔ (bitsValue x).toNat.Prime := by
  have hfit : 2<2^n := by
    have := Nat.pow_le_pow_right (n:=2) (by decide) hn
    norm_num at this
    omega
  rw [primeWord,eval_band,Bool.and_eq_true,wordLe_eval,wordConstant_eval,
    eval_select,Function.comp_id,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hfit,decide_eq_true_eq,
    eval_comp]
  by_cases h : 2≤(bitsValue x).toNat
  · rw [and_iff_right h,primalityNet_correct hn _ (by
      rw [resizeWord_toNat (rootWidth_ge n)];exact h) (by
      rw [resizeWord_toNat (rootWidth_ge n)];exact (bitsValue x).isLt),
      resizeWord_toNat (rootWidth_ge n)]
  · constructor
    · exact fun hh => (h hh.1).elim
    · exact fun hh => (h hh.two_le).elim

lemma primeWord_count (n : ℕ) : (primeWord n).net.count≤
    49*n+10+rootWidth n+primalityBound n := by
  have h₁ := wordLe_count (wordConstant (n:=n) (BitVec.ofNat n 2)) (select id)
  have h₂ := resizeWord_count n (rootWidth n)
  have h₃ := primalityNet_count n
  rw [wordConstant_count,count_select] at h₁
  simp only [primeWord,count_band,count_comp]
  omega

def zeroWord {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k 1 :=
  equalOn a (wordConstant 0)

lemma zeroWord_value {k n : ℕ} (a : BooleanNetwork k n) (x : Basis k) :
    (zeroWord a).eval x 0=true ↔ (bitsValue (a.eval x)).toNat=0 := by
  rw [zeroWord,equalOn_value,wordConstant_eval]
  simp

def primeOrZero {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (zeroWord a).bor (a.comp (primeWord n))

lemma primeOrZero_value {k n : ℕ} (hn : 128≤n) (a : BooleanNetwork k n) (x : Basis k) :
    (primeOrZero a).eval x 0=true ↔
      (bitsValue (a.eval x)).toNat=0 ∨ (bitsValue (a.eval x)).toNat.Prime := by
  rw [primeOrZero,eval_bor,Bool.or_eq_true,zeroWord_value,eval_comp,primeWord_value hn]

def paddedPair {k n : ℕ} (a b : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (zeroWord b).bor ((zeroWord a).bnot.band (wordLe a b))

lemma paddedPair_value {k n : ℕ} (a b : BooleanNetwork k n) (x : Basis k) :
    (paddedPair a b).eval x 0=true ↔
      PaddedOrder (bitsValue (a.eval x)).toNat (bitsValue (b.eval x)).toNat := by
  rw [paddedPair,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,bnot_value,
    zeroWord_value,zeroWord_value,wordLe_eval,decide_eq_true_eq]
  rfl

def unpadWord {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k n :=
  wordMux (zeroWord a) (wordConstant 1) a

lemma unpadWord_value {k n : ℕ} (hn : 0<n) (a : BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((unpadWord a).eval x)).toNat=
      if (bitsValue (a.eval x)).toNat=0 then 1 else (bitsValue (a.eval x)).toNat := by
  have hp : 1<2^n := Nat.one_lt_pow (by omega) (by decide)
  rw [unpadWord,wordMux_eval]
  by_cases h : (bitsValue (a.eval x)).toNat=0
  · rw [ite_eq_left h,ite_eq_left ((zeroWord_value a x).mpr h),wordConstant_eval]
    simpa using (Nat.mod_eq_of_lt hp)
  · rw [ite_eq_right h,ite_eq_right (by simpa only [zeroWord_value] using h)]

/-- Multiplication is modulo the sufficiently wide product register; no
repetition of earlier expression DAGs occurs in this linear fold. -/
def productNet {k w : ℕ} : List (BooleanNetwork k w) → BooleanNetwork k w
  | [] => wordConstant 1
  | a::as => (a.pair (productNet as)).comp (mul w)

lemma productNet_value {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    bitsValue ((productNet as).eval x)=(as.map (fun a => bitsValue (a.eval x))).prod := by
  induction as with
  | nil => simp [productNet,wordConstant_eval]
  | cons a as ih => simp only [productNet,eval_comp,eval_pair,mul_word,ih,List.map_cons,List.prod_cons]

lemma productNet_nat {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((productNet as).eval x)).toNat=
      (as.map (fun a => (bitsValue (a.eval x)).toNat)).prod % 2^w := by
  induction as with
  | nil => simp [productNet,wordConstant_eval]
  | cons a as ih =>
    simp only [productNet,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,ih,
      List.map_cons,List.prod_cons,Nat.mul_mod_mod]

def candidateWords {k n : ℕ} (as : Fin n→BooleanNetwork k n) (x : Basis k) : List ℕ :=
  List.ofFn (fun i => (bitsValue ((as i).eval x)).toNat)

def candidateProduct {k n : ℕ} (as : Fin n→BooleanNetwork k n) : BooleanNetwork k (rootWidth n) :=
  productNet (List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n))))

lemma candidateProduct_value {k n : ℕ} (hn : 0<n) (as : Fin n→BooleanNetwork k n) (x : Basis k) :
    (bitsValue ((candidateProduct as).eval x)).toNat=unpadProduct (candidateWords as x) := by
  have he : ((List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n)))).map
      (fun a => (bitsValue (a.eval x)).toNat)) =
      (candidateWords as x).map (fun a => if a=0 then 1 else a) := by
    simp only [List.map_ofFn,candidateWords]
    congr 1
    funext i
    simp only [Function.comp_apply,eval_comp,resizeWord_toNat (rootWidth_ge n),
      unpadWord_value hn]
  have hb : unpadProduct (candidateWords as x)≤(2^n)^n := by
    have hh := List.prod_le_pow_length ((candidateWords as x).map (fun a => if a=0 then 1 else a))
      (2^n) (by
        intro a ha
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
        split
        · exact Nat.one_le_pow _ _ (by decide)
        · exact (bitsValue ((as i).eval x)).isLt.le)
    simpa only [unpadProduct,List.length_map,candidateWords,List.length_ofFn] using hh
  have hpow : (2^n)^n<2^(rootWidth n) := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) (by dsimp [rootWidth];nlinarith)
  rw [candidateProduct,productNet_nat,he]
  change unpadProduct (candidateWords as x) % 2^rootWidth n = _
  exact Nat.mod_eq_of_lt (hb.trans_lt hpow)

def factorVerifierOn {k n : ℕ} (N : BooleanNetwork k n) (as : Fin n→BooleanNetwork k n) :
    BooleanNetwork k 1 :=
  ((all (List.ofFn (fun i => primeOrZero (as i)))).band
    (all (List.ofFn (fun i : Fin (n*n) =>
      let p := finProdFinEquiv.symm i
      if p.1<p.2 then paddedPair (as p.1) (as p.2) else constant true)))).band
    (equalOn (candidateProduct as) (N.comp (resizeWord n (rootWidth n))))

lemma factorVerifierOn_correct {k n : ℕ} (hn : 128≤n) (N : BooleanNetwork k n)
    (as : Fin n→BooleanNetwork k n) (x : Basis k) :
    (factorVerifierOn N as).eval x 0=true ↔
      CorrectEncoding (bitsValue (N.eval x)).toNat n (candidateWords as x) := by
  rw [← factorListValid_iff (by simp [candidateWords]),FactorListValid]
  rw [factorVerifierOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    all_ofFn_eval,all_ofFn_eval,equalOn_value]
  rw [candidateProduct_value (by omega),eval_comp,resizeWord_toNat (rootWidth_ge n)]
  have hp : (∀ i : Fin n, (primeOrZero (as i)).eval x 0=true) ↔
      ∀ a ∈ candidateWords as x, a=0 ∨ a.Prime := by
    simp only [candidateWords,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
      primeOrZero_value hn]
  have hs : (∀ i : Fin (n*n),
      (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
        paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
        else constant true).eval x 0=true) ↔ (candidateWords as x).Pairwise PaddedOrder := by
    rw [candidateWords,List.pairwise_ofFn]
    constructor
    · intro h i j hij
      have hh := h (finProdFinEquiv (i,j))
      simp only [Equiv.symm_apply_apply,ite_eq_left hij] at hh
      exact (paddedPair_value _ _ _).mp hh
    · intro h i
      split_ifs with hij
      · exact (paddedPair_value _ _ _).mpr (h hij)
      · simp
  rw [hp,hs]
  tauto

end ExactQuantumFactoring.BitArithmetic


end

end OAI
