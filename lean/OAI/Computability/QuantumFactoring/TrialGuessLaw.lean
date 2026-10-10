import Mathlib
import OAI.Computability.QuantumFactoring.FairLabelMass
import OAI.Computability.QuantumFactoring.TrialRetentionBounds

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness

abbrev Guesses (n : ℕ) := Basis n × (Basis n × (Basis n × Basis (retentionBits n)))

noncomputable def guessState (n : ℕ) : Guesses n→ℂ :=
  independentState (fairState n) (independentState (fairState n)
    (independentState (fairState n) (fairState (retentionBits n))))

def Retains {n : ℕ} (p : ℚ) (c : Basis (retentionBits n)) : Prop :=
  (bitsValue c).toNat<(Int.floor (p*(2:ℚ)^(retentionBits n))).toNat

noncomputable def firstPass (n d j : ℕ) (x : Guesses n) : Prop :=
  Retains (firstRetention n d j) x.2.2.2
noncomputable def secondPass (n d j : ℕ) (x : Guesses n) : Prop :=
  (bitsValue x.1).toNat=d ∧ (bitsValue x.2.1).toNat=j ∧
    (bitsValue x.2.2.1).toNat<d ∧
      Retains (discrepancyRetention n d j (bitsValue x.2.2.1).toNat) x.2.2.2
noncomputable def thirdPass (n d j : ℕ) (x : Guesses n) : Prop :=
  (bitsValue x.1).toNat=d ∧ (bitsValue x.2.1).toNat=j ∧
    Retains (remainderRetention n d j) x.2.2.2

lemma guess_normalized (n : ℕ) : ∑ x : Guesses n, Complex.normSq (guessState n x)=1 := by
  have h₁ := RecordedHistory.append_normalized (fairState n) (fun _ => fairState (retentionBits n))
    (fair_normalized n) (fun _ => fair_normalized _)
  have h₂ := RecordedHistory.append_normalized (fairState n)
    (fun _ => independentState (fairState n) (fairState (retentionBits n)))
    (fair_normalized n) (fun _ => h₁)
  exact RecordedHistory.append_normalized (fairState n)
    (fun _ => independentState (fairState n) (independentState (fairState n) (fairState (retentionBits n))))
    (fair_normalized n) (fun _ => h₂)

lemma firstPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ) :
    outcomeMass (firstPass n d j) (guessState n)=(firstRetention n d j:ℝ) := by
  unfold firstPass guessState
  rw [independent_mass_right (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => Retains (firstRetention n d j) x.2.2) (fair_normalized n),
    independent_mass_right (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => Retains (firstRetention n d j) x.2) (fair_normalized n),
    independent_mass_right (fairState n) (fairState (retentionBits n)) (Retains (n:=n) (firstRetention n d j)) (fair_normalized n)]
  exact dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j 0).1
    (first_remainder_bounds hn hd hdB j).1 (first_remainder_bounds hn hd hdB j).2.1

lemma secondPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n)
    (j : ℕ) (hj : j<d) :
    outcomeMass (secondPass n d j) (guessState n)=
      (1/((2:ℝ)^n)^3)*∑ t ∈ Finset.range d, (discrepancyRetention n d j t:ℝ) := by
  unfold secondPass guessState
  rw [
    independent_mass (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => (bitsValue x).toNat=d)
      (fun x => (bitsValue x.1).toNat=j ∧ (bitsValue x.2.1).toNat<d ∧
        Retains (discrepancyRetention n d j (bitsValue x.2.1).toNat) x.2.2),fair_value_mass hdB,
    independent_mass (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => (bitsValue x).toNat=j)
      (fun x => (bitsValue x.1).toNat<d ∧ Retains (discrepancyRetention n d j (bitsValue x.1).toNat) x.2),
    fair_value_mass (hj.trans hdB),
    fair_variable_append hdB.le (fairState (retentionBits n))
      (fun t => Retains (n:=n) (discrepancyRetention n d j t))]
  have he : (∑ t ∈ Finset.range d,
      outcomeMass (Retains (n:=n) (discrepancyRetention n d j t)) (fairState (retentionBits n)))=
      ∑ t ∈ Finset.range d, (discrepancyRetention n d j t:ℝ) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j t).2.1
      (all_retention_bounds hn hd hdB j (Finset.mem_range.mp ht)).2.1.1
      (all_retention_bounds hn hd hdB j (Finset.mem_range.mp ht)).2.1.2
  rw [he]
  ring

lemma thirdPass_mass {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n)
    (j : ℕ) (hj : j<d) :
    outcomeMass (thirdPass n d j) (guessState n)=
      (1/((2:ℝ)^n)^2)*(remainderRetention n d j:ℝ) := by
  unfold thirdPass guessState
  rw [
    independent_mass (fairState n) (independentState (fairState n)
      (independentState (fairState n) (fairState (retentionBits n))))
      (fun x => (bitsValue x).toNat=d)
      (fun x => (bitsValue x.1).toNat=j ∧ Retains (remainderRetention n d j) x.2.2),fair_value_mass hdB,
    independent_mass (fairState n) (independentState (fairState n) (fairState (retentionBits n)))
      (fun x => (bitsValue x).toNat=j)
      (fun x => Retains (remainderRetention n d j) x.2),fair_value_mass (hj.trans hdB),
    independent_mass_right (fairState n) (fairState (retentionBits n)) (Retains (n:=n) (remainderRetention n d j)) (fair_normalized n)]
  have he : outcomeMass (Retains (n:=n) (remainderRetention n d j)) (fairState (retentionBits n))=
      (remainderRetention n d j:ℝ) :=
    dyadic_fair_threshold (retentions_fixedDenominator hn hdB.le j 0).2.2
      (all_retention_bounds hn hd hdB j hd).2.2.1
      (all_retention_bounds hn hd hdB j hd).2.2.2
  rw [he]
  ring

end ExactQuantumFactoring.OrderTrial


end

end OAI
