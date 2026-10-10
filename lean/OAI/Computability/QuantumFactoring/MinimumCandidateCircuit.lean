import Mathlib
import OAI.Computability.QuantumFactoring.SamplerDecodeCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

def minNonzero (a b : ℕ) : ℕ := if a=0 then b else if b=0 then a else min a b
lemma minNonzero_options (a b : Option ℕ)
    (ha : ∀ d, a=some d → 0<d) (hb : ∀ d, b=some d → 0<d) :
    minNonzero (a.getD 0) (b.getD 0)=(minOption a b).getD 0 := by
  cases a with
  | none => simp only [Option.getD_none,minNonzero,ite_true,minOption]
  | some a =>
    have hapos : a≠0 := (ha a rfl).ne'
    cases b with
    | none => simp only [Option.getD_none,Option.getD_some,minNonzero,ite_eq_right hapos,ite_true,minOption]
    | some b =>
      have hbpos : b≠0 := (hb b rfl).ne'
      simp only [Option.getD_some,minNonzero,ite_eq_right hapos,ite_eq_right hbpos,minOption]

def minimumChoice (w : ℕ) : BooleanNetwork (w+w) w :=
  let a := leftNet w w
  let b := rightNet w w
  wordMux (equalOn a (wordConstant (BitVec.ofNat w 0))) b
    (wordMux (equalOn b (wordConstant (BitVec.ofNat w 0))) a (wordMux (wordLt a b) a b))
lemma minimumChoice_value {w : ℕ} (a b : Basis w) :
    (bitsValue ((minimumChoice w).eval (Fin.append a b))).toNat=
      minNonzero (bitsValue a).toNat (bitsValue b).toNat := by
  have h₁ := equalOn_value (leftNet w w) (wordConstant (BitVec.ofNat w 0)) (Fin.append a b)
  have h₂ := equalOn_value (rightNet w w) (wordConstant (BitVec.ofNat w 0)) (Fin.append a b)
  simp only [leftNet_eval,rightNet_eval,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod] at h₁ h₂
  simp only [minimumChoice,wordMux_eval,leftNet_eval,rightNet_eval]
  simp only [h₁,h₂,wordLt_eval,leftNet_eval,rightNet_eval,decide_eq_true_eq]
  split_ifs with ha hb hab
  · simp only [minNonzero,ite_eq_left ha]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_left hb]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_right hb,min_eq_left hab.le]
  · simp only [minNonzero,ite_eq_right ha,ite_eq_right hb,min_eq_right (by omega : (bitsValue b).toNat≤(bitsValue a).toNat)]
lemma minimumChoice_count (w : ℕ) : (minimumChoice w).net.count≤300*w+60 := by
  have h₁ := equalOn_count (leftNet w w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  have h₂ := equalOn_count (rightNet w w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  have h₃ := wordLt_count (leftNet w w) (rightNet w w)
  simp only [leftNet,rightNet,count_select,wordConstant_count] at h₁ h₂ h₃
  simp only [minimumChoice,wordMux_count,leftNet,rightNet,count_select]
  omega

/-- Pair costly subnets ONCE before comparing; the recursive minimum is not
copied into each arm of the mux. This gives a linear, not exponential, scan. -/
def minimumNet {k w : ℕ} : {K : ℕ} → (Fin K → BooleanNetwork k w) → BooleanNetwork k w
  | 0,_ => wordConstant (BitVec.ofNat w 0)
  | _+1,f => ((f 0).pair (minimumNet (fun i => f i.succ))).comp (minimumChoice w)
lemma minimumNet_value {k w K : ℕ} (f : Fin K → BooleanNetwork k w) (x : Basis k)
    (g : Fin K → Option ℕ) (h : ∀ i,(bitsValue ((f i).eval x)).toNat=(g i).getD 0)
    (hp : ∀ i d,g i=some d→0<d) :
    (bitsValue ((minimumNet f).eval x)).toNat=(minimumCandidate (List.ofFn g)).getD 0 := by
  induction K with
  | zero => simp only [minimumNet,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,
      List.ofFn_zero,minimumCandidate,Option.getD_none]
  | succ K ih =>
    rw [minimumNet,eval_comp,eval_pair,minimumChoice_value,h 0,
      ih (fun i=>f i.succ) (fun i=>g i.succ) (fun i=>h i.succ) (fun i=>hp i.succ),
      List.ofFn_succ,minimumCandidate]
    apply minNonzero_options _ _ (hp 0)
    intro d hd
    have hh := minimumCandidate_mem hd
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hh
    exact hp i.succ d hi
lemma minimumNet_count {k w K c : ℕ} (f : Fin K → BooleanNetwork k w)
    (h : ∀ i,(f i).net.count≤c) : (minimumNet f).net.count≤w+K*(c+300*w+60) := by
  induction K with
  | zero => simp only [minimumNet,wordConstant_count,zero_mul,add_zero,le_refl]
  | succ K ih =>
    have hh := ih (fun i=>f i.succ) (fun i=>h i.succ)
    have hc := minimumChoice_count w
    rw [minimumNet,count_comp,count_pair]
    have h0 := h 0
    nlinarith

end ExactQuantumFactoring.OrderTrial


end

end OAI
