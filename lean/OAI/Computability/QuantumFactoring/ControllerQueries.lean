import Mathlib
import OAI.Computability.QuantumFactoring.ProvidedSplits

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.FactorController

/-- The actual queried moduli, in chronological order. A rejected divisor
aborts and does not query nonexistent later work. -/
def queries (choose : ℕ→ℕ→ℕ) : ℕ→ℕ→List ℕ→List (ℕ×ℕ)
  | _, _, [] => []
  | 0, _, _::_ => []
  | fuel+1, i, m::ms =>
    if m.Prime then queries choose fuel (i+1) ms
    else (i,m)::(if ProperDivisor m (choose i m) then
      queries choose fuel (i+1) (choose i m::m/choose i m::ms) else [])

lemma queries_length (choose : ℕ→ℕ→ℕ) (fuel i : ℕ) (ms : List ℕ) :
    (queries choose fuel i ms).length ≤ fuel := by
  induction fuel generalizing i ms with
  | zero => cases ms <;> simp [queries]
  | succ fuel ih =>
    cases ms with
    | nil => simp [queries]
    | cons m ms =>
      simp only [queries]
      split_ifs with hp hd
      · exact (ih _ _).trans (by omega)
      · simpa only [List.length_cons] using Nat.succ_le_succ (ih (i+1) _)
      · simp

/-- All-good is required ONLY at queries of this very run, not at a table of
counterfactual future requests. Exhaustion is excluded by the split weight. -/
theorem run_complete_on_queries (choose : ℕ→ℕ→ℕ) {fuel i : ℕ} {ms : List ℕ}
    (hms : ∀ m∈ms, 2 ≤ m) (hw : weight ms ≤ fuel)
    (hg : ∀ im∈queries choose fuel i ms, ProperDivisor im.2 (choose im.1 im.2)) :
    ∃ ps, run choose fuel i ms=some ps := by
  induction fuel generalizing i ms with
  | zero =>
    cases ms with
    | nil => exact ⟨[],rfl⟩
    | cons m ms =>
      have hp := splitWeight_pos (hms m (by simp))
      simp only [weight,List.map_cons,List.sum_cons] at hw
      omega
  | succ fuel ih =>
    cases ms with
    | nil => exact ⟨[],rfl⟩
    | cons m ms =>
      have hm := hms m (by simp)
      have ht : ∀ a∈ms,2 ≤ a := fun a ha => hms a (by simp [ha])
      by_cases hp : m.Prime
      · have hw' : weight ms ≤ fuel := by rw [weight_prime m ms hp] at hw; omega
        have hg' : ∀ im∈queries choose fuel (i+1) ms, ProperDivisor im.2 (choose im.1 im.2) := by
          intro im hi
          exact hg im (by simpa only [queries,ite_eq_left hp] using hi)
        obtain ⟨ps,hps⟩ := ih ht hw' hg'
        exact ⟨m::ps,by simp only [run,ite_eq_left hp,hps,Option.map_some]⟩
      · have hd := hg (i,m) (by simp only [queries,ite_eq_right hp,List.mem_cons]; exact Or.inl trivial)
        have hd' : ProperDivisor m (choose i m) := hd
        have hq := hd'.quotient
        have hw' : weight (choose i m::m/choose i m::ms) ≤ fuel := by
          rw [weight_split hd' ms] at hw
          omega
        have hm' : ∀ a∈choose i m::m/choose i m::ms,2 ≤ a := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · have := hd'.1; omega
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact hq.1
            · exact ht a ha
        have hg' : ∀ im∈queries choose fuel (i+1) (choose i m::m/choose i m::ms),
            ProperDivisor im.2 (choose im.1 im.2) := by
          intro im hi
          exact hg im (by simp only [queries,ite_eq_right hp,ite_eq_left hd',List.mem_cons]; exact Or.inr hi)
        obtain ⟨ps,hps⟩ := ih hm' hw' hg'
        exact ⟨ps,by simp only [run,ite_eq_right hp,ite_eq_left hd',hps]⟩

lemma queries_bounded (choose : ℕ→ℕ→ℕ) {fuel i N : ℕ} {ms : List ℕ}
    (hms : ∀ m∈ms,2 ≤ m ∧ m ≤ N) :
    ∀ im∈queries choose fuel i ms, 2 ≤ im.2 ∧ im.2 ≤ N ∧ ¬im.2.Prime := by
  induction fuel generalizing i ms with
  | zero => cases ms <;> simp [queries]
  | succ fuel ih =>
    cases ms with
    | nil => simp [queries]
    | cons m ms =>
      have hm := hms m (by simp)
      have ht : ∀ a∈ms,2 ≤ a ∧ a ≤ N := fun a ha => hms a (by simp [ha])
      simp only [queries]
      split_ifs with hp hd
      · exact ih ht
      · intro im hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨hm.1,hm.2,hp⟩
        · apply ih (ms:=choose i m::m/choose i m::ms) ?_ im hi
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨by have := hd.1; omega,hd.2.1.le.trans hm.2⟩
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨hd.quotient.1,hd.quotient.2.1.le.trans hm.2⟩
            · exact ht a ha
      · intro im hi
        have he : im=(i,m) := by simpa only [List.mem_singleton] using hi
        subst im
        exact ⟨hm.1,hm.2,hp⟩

/-- Instantiate the local event with the source's favorable list and actual
true-order outputs. Only recorded queries, no counterfactual oracle inputs. -/
theorem supplied_node_complete_on_queries {N n : ℕ} (hN : 2 ≤ N) (hb : N < 2^n)
    (outputs : ℕ→ℕ→List (ℕ×ℕ))
    (hg : ∀ im∈queries (fun i m => suppliedDivisor m n (outputs i m)) (2*n) 0 [N],
      ∀ (hm : 2 ≤ im.2) (hle : im.2 ≤ N), Odd im.2 → ¬Primality.PerfectPower im.2 →
      ∃ (p₀ : Component im.2) (u : (ZMod im.2)ˣ),
        FavorableUnit (by omega : im.2≠0) (hle.trans_lt hb) p₀ u ∧
        ((u : ZMod im.2).val,orderOf u)∈outputs im.1 im.2) :
    ∃ ps, run (fun i m => suppliedDivisor m n (outputs i m)) (2*n) 0 [N]=some ps := by
  apply run_complete_on_queries _ (by
    intro m hm
    have he : m=N := by simpa using hm
    subst m
    exact hN)
  · have hh := AuxiliaryTree.splitWeight_bound (by omega) hb
    simp only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    omega
  · intro im hi
    have hbounds := queries_bounded (fun i m => suppliedDivisor m n (outputs i m))
      (N:=N) (by
        intro m hm
        have he : m=N := by simpa using hm
        subst m
        exact ⟨hN,le_rfl⟩) im hi
    exact suppliedDivisor_good hbounds.1 (hbounds.2.1.trans_lt hb) hbounds.2.2 _
      (hg im hi hbounds.1 hbounds.2.1)

end ExactQuantumFactoring.FactorController


end

end OAI
