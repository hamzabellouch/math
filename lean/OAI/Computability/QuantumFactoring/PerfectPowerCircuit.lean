import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityCorrectness
import OAI.Computability.QuantumFactoring.BooleanFold
import OAI.Computability.QuantumFactoring.RootCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Check a candidate root against the input integer, with its static exponent. -/
def rootCheck (w e : ℕ) : BooleanNetwork (w+w) 1 :=
  (wordLe (wordConstant (BitVec.ofNat w 2)) (rootGuess w)).band
    ((((rootGuess w).comp (staticPower w e)).pair (rootModulus w)).comp (wordEq w))

lemma rootCheck_eval (w e : ℕ) (m g : Basis w) :
    (rootCheck w e).eval (Fin.append m g) 0=true ↔
      2 % 2^w ≤ (bitsValue g).toNat ∧
        (bitsValue g).toNat^e % 2^w = (bitsValue m).toNat := by
  rw [rootCheck,eval_band,wordLe_eval,wordConstant_eval,rootGuess_eval,
    eval_comp,eval_pair,wordEq_eval,eval_comp,staticPower_eval,rootGuess_eval,rootModulus_eval]
  simp only [Bool.and_eq_true,decide_eq_true_eq,BitVec.toNat_ofNat]
  constructor
  · rintro ⟨hle,h⟩
    refine ⟨hle,?_⟩
    simpa only [BitVec.toNat_pow] using congrArg BitVec.toNat h
  · rintro ⟨hle,h⟩
    refine ⟨hle,?_⟩
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_pow] using h

def exponentCheck (n e : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  ((select id).pair (boundedRootNet n e)).comp (rootCheck (rootWidth n) e)

lemma exponentCheck_eval {n e : ℕ} (hn : 2 ≤ n) (he : 2 ≤ e) (hen : e ≤ n)
    (m : Basis (rootWidth n)) (hm : (bitsValue m).toNat < 2^n) :
    (exponentCheck n e).eval m 0=true ↔
      2 ≤ Primality.boundedRoot (bitsValue m).toNat e n ∧
      (Primality.boundedRoot (bitsValue m).toNat e n)^e=(bitsValue m).toNat := by
  rw [exponentCheck,eval_comp,eval_pair,eval_select,Function.comp_id,rootCheck_eval,
    boundedRootNet_value n e hen]
  have hp : 2 < 2^(rootWidth n) := by
    have hh : 1 < rootWidth n := by dsimp [rootWidth]; nlinarith
    exact lt_of_eq_of_lt (by norm_num : 2=2^1) (Nat.pow_lt_pow_right (by decide) hh)
  have hroot := (Primality.boundedRoot_spec (by omega : 0 < e) hm).1
  have hmn : n ≤ rootWidth n := by dsimp [rootWidth];nlinarith
  rw [Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt
    (hroot.trans_lt (hm.trans_le (Nat.pow_le_pow_right (by decide) hmn)))]

def perfectPowerNet (n : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  any (List.ofFn (fun e : Fin (n+1) => if 2 ≤ e.val then exponentCheck n e.val else constant false))

/-- The complete first AKS rejection check, as an actual polynomial-size
Boolean circuit: exponents2..n and n exact bounded binary-root steps each. -/
theorem perfectPowerNet_correct {n : ℕ} (hn : 2 ≤ n) (m : Basis (rootWidth n))
    (hm : (bitsValue m).toNat < 2^n) :
    (perfectPowerNet n).eval m 0=true ↔ Primality.PerfectPower (bitsValue m).toNat := by
  rw [perfectPowerNet,any_eval]
  constructor
  · rintro ⟨c,hc,hv⟩
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hc
    by_cases he : 2 ≤ e.val
    · rw [ite_eq_left he] at hv
      have hh := (exponentCheck_eval hn he (by omega) m hm).mp hv
      exact ⟨_,e.val,hh.1,he,hh.2⟩
    · simp [he] at hv
  · rintro ⟨b,e,hb,he,hbm⟩
    have hen : e < n := Primality.perfectPower_exponent_lt hm hb hbm
    have hr := Primality.boundedRoot_pow_eq (by omega : 0 < e) hm hbm
    refine ⟨exponentCheck n e,?_,?_⟩
    · apply List.mem_ofFn.mpr
      exact ⟨⟨e,by omega⟩,ite_eq_left he⟩
    · rw [exponentCheck_eval hn he (by omega) m hm,hr]
      exact ⟨hb,hbm⟩

lemma rootCheck_count (w e : ℕ) : (rootCheck w e).net.count ≤
    146*w+31+e*(90*w*w+14*w+6) := by
  have h₁ := wordLe_count (wordConstant (n := w+w) (BitVec.ofNat w 2)) (rootGuess w)
  have h₂ := wordEq_count w
  have h₃ := staticPower_count w e
  simp only [rootGuess,count_select,wordConstant_count] at h₁
  simp only [rootCheck,count_band,count_comp,count_pair,rootGuess,rootModulus,count_select,
    zero_add,add_zero]
  omega

abbrev perfectCheckBound (n : ℕ) : ℕ :=
  147*rootWidth n+31+n*(230*rootWidth n+21+n*(90*rootWidth n*rootWidth n+14*rootWidth n+6))+
    n*(90*rootWidth n*rootWidth n+14*rootWidth n+6)

lemma exponentCheck_count (n e : ℕ) (he : e ≤ n) : (exponentCheck n e).net.count ≤
    perfectCheckBound n := by
  have h₁ := boundedRootNet_count n e
  have h₂ := rootCheck_count (rootWidth n) e
  have h₃ := Nat.mul_le_mul_right (90*rootWidth n*rootWidth n+14*rootWidth n+6) he
  have h₄ := Nat.mul_le_mul_left n h₃
  simp only [exponentCheck,count_comp,count_pair,count_select,zero_add]
  dsimp [perfectCheckBound]
  nlinarith

lemma perfectExponent_count (n : ℕ) (e : Fin (n+1)) :
    (if 2 ≤ e.val then exponentCheck n e.val else
      (constant false : BooleanNetwork (rootWidth n) 1)).net.count ≤ perfectCheckBound n := by
  by_cases he : 2 ≤ e.val
  · have hh := congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count)
      (ite_eq_left he : (if 2 ≤ e.val then exponentCheck n e.val else constant false)=exponentCheck n e.val)
    exact hh.trans_le (exponentCheck_count n e.val (by omega))
  · have hh := congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count)
      (ite_eq_right he : (if 2 ≤ e.val then exponentCheck n e.val else constant false)=constant false)
    apply hh.trans_le
    change 1 ≤ perfectCheckBound n
    dsimp [perfectCheckBound,rootWidth]
    omega

lemma perfectPowerNet_count (n : ℕ) : (perfectPowerNet n).net.count ≤
    (n+1)*(perfectCheckBound n+4)+1 := by
  have h := any_count (c := perfectCheckBound n)
    (List.ofFn (fun e : Fin (n+1) => if 2 ≤ e.val then exponentCheck n e.val else constant false)) (by
      intro c hc
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hc
      exact perfectExponent_count n e)
  simpa only [perfectPowerNet,List.length_ofFn] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
