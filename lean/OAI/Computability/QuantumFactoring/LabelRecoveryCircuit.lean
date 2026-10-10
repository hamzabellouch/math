import Mathlib
import OAI.Computability.QuantumFactoring.BinLabelCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- A bounded scan; either the sole valid label, or the distinguished zero pair. -/
def scanPairs (Q B k : ℕ) : ℕ → ℕ×ℕ
  | 0 => (0,0)
  | i+1 => let a := checkedPair Q B k i
           if a.1≠0 then a else scanPairs Q B k i

lemma scanPairs_success {Q B k K : ℕ} :
    (scanPairs Q B k K).1≠0 ↔ ∃ i<K, (checkedPair Q B k i).1≠0 := by
  induction K with
  | zero => simp [scanPairs]
  | succ K ih =>
    simp only [scanPairs]
    split_ifs with h
    · exact ⟨fun _ => ⟨K,by omega,h⟩,fun _ => h⟩
    · rw [ih]
      constructor
      · rintro ⟨i,hi,hx⟩; exact ⟨i,by omega,hx⟩
      · rintro ⟨i,hi,hx⟩
        refine ⟨i,?_,hx⟩
        by_contra hh
        have he : i=K := by omega
        exact h (he ▸ hx)

lemma scanPairs_sound {Q B k K : ℕ} (h : (scanPairs Q B k K).1≠0) :
    IsBinLabel Q B k (scanPairs Q B k K) := by
  induction K with
  | zero => simp [scanPairs] at h
  | succ K ih =>
    simp only [scanPairs] at h ⊢
    split_ifs at h ⊢ with hh
    · exact checkedPair_sound hh
    · exact ih h

lemma scanPairs_complete {s Q B k : ℕ} {l : ℕ×ℕ} (hQ : B^2≤Q) (hsize : Q<2^s)
    (hl : IsBinLabel Q B k l) : scanPairs Q B k (2*s+1)=l := by
  obtain ⟨_,i,hi,he⟩ := mem_recoveredLabels.mp (recoveredLabels_complete hQ hsize hl)
  rw [convergentPair_label] at he
  have hh : (checkedPair Q B k i).1≠0 := checkedPair_nonzero_iff.mpr (he ▸ hl)
  have hs := scanPairs_success.mpr (⟨i,by omega,hh⟩ : ∃ i<2*s+1, (checkedPair Q B k i).1≠0)
  exact (scanPairs_sound hs).unique hQ hl

/-- Choose the left nonzero-denominator pair, otherwise the right. The costly
candidate and recursive scan are paired ONCE before this inexpensive mux. -/
def pairChoice (w : ℕ) : BooleanNetwork ((w+w)+(w+w)) (w+w) :=
  let left := rootModulus (w+w)
  let right := rootGuess (w+w)
  let den := left.comp (rootModulus w)
  let zero := equalOn den (wordConstant (BitVec.ofNat w 0))
  wordMux zero right left

lemma pairChoice_eval {w : ℕ} (a b c d : Basis w) :
    (pairChoice w).eval (Fin.append (Fin.append a b) (Fin.append c d))=
      if (bitsValue a).toNat=0 then Fin.append c d else Fin.append a b := by
  rw [pairChoice,wordMux_eval]
  simp only [rootModulus_eval,rootGuess_eval]
  have he := equalOn_value
    ((rootModulus (w+w)).comp (rootModulus w))
    (wordConstant (n:=(w+w)+(w+w)) (BitVec.ofNat w 0))
    (Fin.append (Fin.append a b) (Fin.append c d))
  simp only [eval_comp,rootModulus_eval,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod] at he
  simp only [he]

lemma pairChoice_count (w : ℕ) : (pairChoice w).net.count ≤ 120*w+31 := by
  have hc := equalOn_count ((rootModulus (w+w)).comp (rootModulus w))
    (wordConstant (n:=(w+w)+(w+w)) (BitVec.ofNat w 0))
  simp only [rootModulus,count_select,count_comp,wordConstant_count,zero_add] at hc
  simp only [pairChoice,wordMux_count,rootGuess,rootModulus,count_select]
  omega

def recoveryNet {n w : ℕ} (Q B k : BooleanNetwork n w) : ℕ → BooleanNetwork n (w+w)
  | 0 => (wordConstant (BitVec.ofNat w 0)).pair (wordConstant (BitVec.ofNat w 0))
  | i+1 => ((checkedConvergent i Q B k).pair (recoveryNet Q B k i)).comp (pairChoice w)

lemma recoveryNet_value {n s w : ℕ} (Q B k : BooleanNetwork n w) (K : ℕ)
    (hw : cfWidth s K≤w) (x : Basis n)
    (hQ : (bitsValue (Q.eval x)).toNat<2^s) (hk : (bitsValue (k.eval x)).toNat<2^s) :
    ∃ d j : Basis w, (recoveryNet Q B k K).eval x=Fin.append d j ∧
      ((bitsValue d).toNat,(bitsValue j).toNat)=scanPairs
        (bitsValue (Q.eval x)).toNat (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat K := by
  induction K with
  | zero =>
    let z := (wordConstant (n:=n) (BitVec.ofNat w 0)).eval x
    refine ⟨z,z,?_,?_⟩
    · exact eval_pair _ _ x
    · simp [z,scanPairs,wordConstant_eval]
  | succ K ih =>
    have hwK : cfWidth s K≤w := by unfold cfWidth at *; nlinarith
    obtain ⟨c,d,hcd,hcdv⟩ := ih hwK
    obtain ⟨a,b,hab,habv⟩ := checkedConvergent_value K hwK Q B k x hQ hk
    have hs : (recoveryNet Q B k (K+1)).eval x=
        if (bitsValue a).toNat=0 then Fin.append c d else Fin.append a b := by
      rw [recoveryNet,eval_comp,eval_pair,hab,hcd,pairChoice_eval]
    have hv : (bitsValue a).toNat=(checkedPair (bitsValue (Q.eval x)).toNat
        (bitsValue (B.eval x)).toNat (bitsValue (k.eval x)).toNat K).1 := congrArg Prod.fst habv
    by_cases ha : (bitsValue a).toNat=0
    · refine ⟨c,d,by rw [hs,ite_eq_left ha],?_⟩
      rw [scanPairs,ite_eq_right (by simpa [← hv] using ha),hcdv]
    · refine ⟨a,b,by rw [hs,ite_eq_right ha],?_⟩
      rw [scanPairs,ite_eq_left (by simpa [← hv] using ha)]
      exact habv

end ExactQuantumFactoring.OrderTrial


end

end OAI
