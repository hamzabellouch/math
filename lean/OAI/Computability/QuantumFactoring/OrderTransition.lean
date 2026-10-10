import Mathlib
import OAI.Computability.QuantumFactoring.RepeatedTrials
import OAI.Computability.QuantumFactoring.OrderCandidateLaw

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness RepeatedTrials

def minOption : Option ℕ→Option ℕ→Option ℕ
  | none,b => b
  | some a,none => some a
  | some a,some b => some (min a b)

def minimumCandidate : List (Option ℕ)→Option ℕ
  | [] => none
  | a::as => minOption a (minimumCandidate as)

lemma minOption_some_mem {a b : Option ℕ} {d : ℕ} (h : minOption a b=some d) :
    a=some d ∨ b=some d := by
  cases a with
  | none => exact Or.inr h
  | some a =>
    cases b with
    | none => exact Or.inl h
    | some b =>
      have he : min a b=d := Option.some.inj h
      by_cases hab : a≤b
      · exact Or.inl (congrArg some ((min_eq_left hab).symm.trans he))
      · exact Or.inr (congrArg some ((min_eq_right (by omega)).symm.trans he))

lemma minimumCandidate_mem {as : List (Option ℕ)} {d : ℕ} (h : minimumCandidate as=some d) :
    some d∈as := by
  induction as with
  | nil => cases h
  | cons a as ih =>
    rcases minOption_some_mem h with hd|hd
    · exact List.mem_cons.mpr (Or.inl hd.symm)
    · exact List.mem_cons.mpr (Or.inr (ih hd))

lemma minimumCandidate_lower {as : List (Option ℕ)} {d r : ℕ}
    (h : ∀ a, some a∈as → r≤a) (hd : minimumCandidate as=some d) : r≤d :=
  h d (minimumCandidate_mem hd)

lemma minOption_eq_low {a b : Option ℕ} {r : ℕ}
    (ha : ∀ d, a=some d → r≤d) (hb : ∀ d, b=some d → r≤d) :
    minOption a b=some r ↔ a=some r ∨ b=some r := by
  constructor
  · exact minOption_some_mem
  · rintro (he|he)
    · subst a
      cases b with
      | none => rfl
      | some d => simp only [minOption,min_eq_left (hb d rfl)]
    · subst b
      cases a with
      | none => rfl
      | some d => simp only [minOption,min_eq_right (ha d rfl)]

lemma minimumCandidate_eq_low {as : List (Option ℕ)} {r : ℕ}
    (h : ∀ a, some a∈as → r≤a) : minimumCandidate as=some r ↔ some r∈as := by
  induction as with
  | nil => simp [minimumCandidate]
  | cons a as ih =>
    have ht : ∀ b, some b∈as → r≤b := fun b hb => h b (List.mem_cons_of_mem a hb)
    rw [minimumCandidate,minOption_eq_low (by
      intro d hd
      exact h d (List.mem_cons.mpr (Or.inl hd.symm))) (fun d hd => minimumCandidate_lower ht hd),ih ht]
    simp only [List.mem_cons,eq_comm]

/-- The source order transition ignores empty trials and returns the least
nonempty candidate, with zero for the entirely empty list. -/
noncomputable def orderResult {w : ℕ} (s n : ℕ) (a m : Basis w) (K : ℕ)
    (x : Fin K→Raw w s n) : ℕ :=
  (minimumCandidate (List.ofFn (fun i => trialResult s n a m (x i)))).getD 0

lemma orderResult_eq_order {w s n K : ℕ} (a m : Basis w) (hm : 2≤(bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (x : Fin K→Raw w s n) :
    orderResult s n a m K x=orderOf u ↔ ∃ i, trialResult s n a m (x i)=some (orderOf u) := by
  have hlow : ∀ d, some d∈List.ofFn (fun i => trialResult s n a m (x i)) → orderOf u≤d := by
    intro d hd
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hd
    have hh := trialResult_multiple a m hm u ha (x i) hi
    exact Nat.le_of_dvd hh.1 hh.2.2
  have he := minimumCandidate_eq_low hlow
  have hr : 0<orderOf u := orderOf_pos u
  have hd : ∀ c : Option ℕ, c.getD 0=orderOf u ↔ c=some (orderOf u) := by
    intro c
    cases c <;> simp [Ne.symm hr.ne']
  rw [orderResult,hd,he]
  simp only [List.mem_ofFn]

/-- Physical repeated law (before the deterministic minimum oracle). -/
theorem orderResult_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (K : ℕ) :
    outcomeMass (fun x => orderResult s n a m K x=orderOf u) (tensorState (rawState s n a m) K)=
      1-(1-(Nat.totient (orderOf u):ℝ)*(prescribedMass (orderOf u):ℝ))^K := by
  have he : (fun x : Fin K→Raw w s n => orderResult s n a m K x=orderOf u)=
      (fun x => ∃ i, trialResult s n a m (x i)=some (orderOf u)) := by
    funext x
    exact propext (orderResult_eq_order a m hm u ha x)
  rw [he,tensor_some_mass (rawState s n a m) K (fun x => trialResult s n a m x=some (orderOf u)) (raw_normalized s n a m),trialResult_mass hn hs a m hm u ha hdB]

/-- Original cutoff, original K=n^5, no extra oracle or changed asymptotics. -/
theorem orderResult_lower {w n s : ℕ} (hn : 128≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) :
    1-1/(2:ℝ)^(2*n)≤outcomeMass (fun x => orderResult s n a m (n^5) x=orderOf u)
      (tensorState (rawState s n a m) (n^5)) := by
  have hn' : 1≤n := by omega
  rw [orderResult_mass hn' hs a m hm u ha hdB]
  have hl := actual_trial_lower hn' hs a m hm u ha hdB
  have hu := (mass_bounds (rawState s n a m) (fun x => trialResult s n a m x=some (orderOf u))
    (raw_normalized s n a m)).2
  rw [trialResult_mass hn' hs a m hm u ha hdB] at hl hu
  exact repeated_success_lower hn hl hu

end ExactQuantumFactoring.OrderTrial


end

end OAI
