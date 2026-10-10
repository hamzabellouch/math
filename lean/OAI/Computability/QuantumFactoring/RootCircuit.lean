import Mathlib
import OAI.Computability.QuantumFactoring.ModularMultiply
import OAI.Computability.QuantumFactoring.ArithmeticPredicates
import OAI.Computability.QuantumFactoring.BinaryRoots

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Width large enough for every candidate's e-th power, e≤n. -/
abbrev rootWidth (n : ℕ) := n*n+1

def rootModulus (w : ℕ) : BooleanNetwork (w+w) w := select (Fin.castAdd w)
def rootGuess (w : ℕ) : BooleanNetwork (w+w) w := select (Fin.natAdd w)

def rootNext (w k : ℕ) : BooleanNetwork (w+w) w :=
  ((rootGuess w).pair (wordConstant (BitVec.ofNat w (2^k)))).comp (add w)

def rootNew (w e k : ℕ) : BooleanNetwork (w+w) w :=
  wordMux (wordLe ((rootNext w k).comp (staticPower w e)) (rootModulus w))
    (rootNext w k) (rootGuess w)

def rootStep (w e k : ℕ) : BooleanNetwork (w+w) (w+w) :=
  (rootModulus w).pair (rootNew w e k)

def rootPrefix (w e : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => select id
  | k+1 => (rootStep w e k).comp (rootPrefix w e k)

lemma rootModulus_eval (w : ℕ) (m g : Basis w) :
    (rootModulus w).eval (Fin.append m g)=m := by
  funext i
  exact Fin.append_left m g i
lemma rootGuess_eval (w : ℕ) (m g : Basis w) :
    (rootGuess w).eval (Fin.append m g)=g := by
  funext i
  exact Fin.append_right m g i

lemma rootNext_word (w k : ℕ) (m g : Basis w) :
    bitsValue ((rootNext w k).eval (Fin.append m g)) =
      bitsValue g + BitVec.ofNat w (2^k) := by
  rw [rootNext,eval_comp,eval_pair,add_word,rootGuess_eval,wordConstant_eval]

lemma rootStep_pack (w e k : ℕ) (m g : Basis w) :
    (rootStep w e k).eval (Fin.append m g) =
      Fin.append m ((rootNew w e k).eval (Fin.append m g)) := by
  rw [rootStep,eval_pair,rootModulus_eval]

lemma rootNext_value {n k : ℕ} (m g : Basis (rootWidth n))
    (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    (bitsValue ((rootNext (rootWidth n) k).eval (Fin.append m g))).toNat =
      (bitsValue g).toNat+2^k := by
  have hn : n < rootWidth n := by dsimp [rootWidth]; nlinarith
  have hp : 2^n < 2^(rootWidth n) := Nat.pow_lt_pow_right (by decide) hn
  have hkp : 2^k < 2^(rootWidth n) :=
    (Nat.pow_le_pow_right (by decide) hk).trans_lt hp
  rw [rootNext_word,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hkp,
    Nat.mod_eq_of_lt (hg.trans_lt hp)]

lemma candidatePower_lt {n e v : ℕ} (he : e ≤ n) (hv : v ≤ 2^n) :
    v^e < 2^(rootWidth n) := by
  have hne : n*e ≤ n*n := Nat.mul_le_mul_left n he
  calc
    v^e ≤ (2^n)^e := Nat.pow_le_pow_left hv e
    _ = 2^(n*e) := (pow_mul 2 n e).symm
    _ ≤ 2^(n*n) := Nat.pow_le_pow_right (by decide) hne
    _ < 2^(rootWidth n) := Nat.pow_lt_pow_right (by decide) (by simp [rootWidth])

lemma rootNew_value {n e k : ℕ} (m g : Basis (rootWidth n))
    (he : e ≤ n) (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    (bitsValue ((rootNew (rootWidth n) e k).eval (Fin.append m g))).toNat =
      if ((bitsValue g).toNat+2^k)^e ≤ (bitsValue m).toNat
      then (bitsValue g).toNat+2^k else (bitsValue g).toNat := by
  have hv := rootNext_value m g hk hg
  rw [rootNew,wordMux_eval,wordLe_eval,eval_comp,staticPower_eval,rootModulus_eval]
  rw [BitVec.toNat_pow,hv,Nat.mod_eq_of_lt (candidatePower_lt he hg)]
  split_ifs <;> simp_all [rootGuess_eval]

lemma rootPrefix_value {n e : ℕ} (m g : Basis (rootWidth n)) (he : e ≤ n)
    (k : ℕ) (hk : k ≤ n) (hg : (bitsValue g).toNat+2^k ≤ 2^n) :
    ∃ z : Basis (rootWidth n),
      (rootPrefix (rootWidth n) e k).eval (Fin.append m g) = Fin.append m z ∧
      (bitsValue z).toNat = Primality.rootSearch (bitsValue m).toNat e k (bitsValue g).toNat := by
  induction k generalizing g with
  | zero => exact ⟨g,rfl,rfl⟩
  | succ k ih =>
    have hg' : (bitsValue g).toNat+2^k ≤ 2^n := by
      have : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    let z := (rootNew (rootWidth n) e k).eval (Fin.append m g)
    have hz : (bitsValue z).toNat =
        if ((bitsValue g).toNat+2^k)^e ≤ (bitsValue m).toNat
        then (bitsValue g).toNat+2^k else (bitsValue g).toNat := rootNew_value m g he (by omega) hg'
    have hzk : (bitsValue z).toNat+2^k ≤ 2^n := by
      rw [hz]
      split_ifs
      · rw [pow_succ] at hg
        omega
      · exact hg'
    obtain ⟨z',hz',hv'⟩ := ih z (by omega) hzk
    refine ⟨z',?_,?_⟩
    · rw [rootPrefix,eval_comp,rootStep_pack]
      exact hz'
    · rw [hv',hz]
      rfl

lemma rootNext_count (w k : ℕ) : (rootNext w k).net.count ≤ 87*w+6 := by
  simp only [rootNext,count_comp,count_pair,rootGuess,count_select,wordConstant_count,zero_add]
  have := add_count w
  omega

lemma rootStep_count (w e k : ℕ) : (rootStep w e k).net.count ≤
    230*w+21+e*(90*w*w+14*w+6) := by
  have h₁ := rootNext_count w k
  have h₂ := staticPower_count w e
  have h₃ := wordLe_count ((rootNext w k).comp (staticPower w e)) (rootModulus w)
  simp only [count_comp,rootModulus,count_select] at h₃
  simp only [rootStep,count_pair,rootModulus,count_select,zero_add,rootNew,wordMux_count,
    rootGuess,count_select,add_zero]
  omega

lemma rootPrefix_count (w e k : ℕ) : (rootPrefix w e k).net.count ≤
    k*(230*w+21+e*(90*w*w+14*w+6)) := by
  induction k with
  | zero => simp [rootPrefix]
  | succ k ih =>
    have h := rootStep_count w e k
    rw [rootPrefix,count_comp]
    nlinarith

def boundedRootNet (n e : ℕ) : BooleanNetwork (rootWidth n) (rootWidth n) :=
  ((select id).pair (wordConstant (BitVec.ofNat (rootWidth n) 0))).comp
    ((rootPrefix (rootWidth n) e n).rewire (Fin.natAdd (rootWidth n)))

lemma boundedRootNet_value (n e : ℕ) (he : e ≤ n) (m : Basis (rootWidth n)) :
    (bitsValue ((boundedRootNet n e).eval m)).toNat =
      Primality.boundedRoot (bitsValue m).toNat e n := by
  let g := (wordConstant (BitVec.ofNat (rootWidth n) 0)).eval m
  have hg : (bitsValue g).toNat=0 := by
    dsimp [g]
    rw [wordConstant_eval]
    simp
  obtain ⟨z,hz,hv⟩ := rootPrefix_value m g he n le_rfl (by rw [hg];omega)
  simp only [boundedRootNet,eval_comp,eval_pair,eval_select,Function.comp_id,eval_rewire]
  change (bitsValue (((rootPrefix (rootWidth n) e n).eval (Fin.append m g)) ∘
    Fin.natAdd (rootWidth n))).toNat = _
  rw [hz]
  have hh : Fin.append m z ∘ Fin.natAdd (rootWidth n)=z := by
    funext i
    exact Fin.append_right m z i
  rw [hh,hv,hg]
  rfl

lemma boundedRootNet_count (n e : ℕ) : (boundedRootNet n e).net.count ≤
    rootWidth n+n*(230*rootWidth n+21+e*(90*rootWidth n*rootWidth n+14*rootWidth n+6)) := by
  have h := rootPrefix_count (rootWidth n) e n
  simp only [boundedRootNet,count_comp,count_pair,count_select,wordConstant_count,
    zero_add,count_rewire]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
