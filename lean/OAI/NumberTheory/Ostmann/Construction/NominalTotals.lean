import OAI.NumberTheory.Ostmann.Conclusion.Scales
import OAI.NumberTheory.Ostmann.Construction.GiantWindowScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

def nominalTail (k : ℕ) (J : ℝ) (Δ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((2:ℝ)^k*J-∑i∈Finset.Ico j k,Δ i)/(2:ℝ)^j

def nominalWeight (k : ℕ) (J : ℝ) (Δ : ℕ → ℝ) (j : ℕ) : ℝ :=
  nominalTail k J Δ j-nominalTail k J Δ (j+1)

theorem nominalTail_end (k : ℕ) (J : ℝ) (Δ : ℕ → ℝ) :
    nominalTail k J Δ k = J := by
  simp [nominalTail]

theorem sum_nominalWeight {k j : ℕ} (hj : j≤k) (J : ℝ) (Δ : ℕ → ℝ) :
    ∑i∈Finset.Ico j k,nominalWeight k J Δ i = nominalTail k J Δ j-J := by
  have h := Finset.sum_Ico_sub (fun i => -nominalTail k J Δ i) hj
  simp only [neg_sub_neg,nominalTail_end] at h
  exact h

theorem nominalTail_step {k j : ℕ} (hj : j<k) (J : ℝ) (Δ : ℕ → ℝ) :
    nominalTail k J Δ j = 2*nominalTail k J Δ (j+1)-Δ j/(2:ℝ)^j := by
  unfold nominalTail
  rw [Finset.sum_eq_sum_Ico_succ_bot hj Δ,pow_succ]
  field_simp
  ring

theorem nominalWeight_recurrence {k j : ℕ} (hj : j<k) (J : ℝ) (Δ : ℕ → ℝ) :
    nominalWeight k J Δ j = J+(∑i∈Finset.Ico (j+1) k,nominalWeight k J Δ i)-Δ j/(2:ℝ)^j := by
  rw [sum_nominalWeight (by omega),nominalWeight,nominalTail_step hj]
  ring

theorem nominalWeight_recurrence_scaled {k j : ℕ} (hj : j<k) (J : ℝ) (Δ : ℕ → ℝ) :
    (2:ℝ)^j*(J+∑i∈Finset.Ico (j+1) k,nominalWeight k J Δ i) =
      (2:ℝ)^j*nominalWeight k J Δ j+Δ j := by
  rw [nominalWeight_recurrence hj]
  field_simp
  ring

theorem nominalWeight_total (k : ℕ) (J : ℝ) (Δ : ℕ → ℝ) :
    J+∑j∈Finset.range k,nominalWeight k J Δ j = (2:ℝ)^k*J-∑j∈Finset.range k,Δ j := by
  rw [Finset.range_eq_Ico,sum_nominalWeight (Nat.zero_le k)]
  simp [nominalTail]

def nominalJ (Bs BD Bz : ℝ) (k : ℕ) (L G₀ c td : ℝ) : ℝ :=
  (Real.log (giantWindowScale ((2:ℝ)^(k+1)) G₀ L:ℝ)-2*c-2*td+
    Conclusion.initialGap Bs k L+∑j∈Finset.range k,Conclusion.stepGap BD Bz k L j)/(2:ℝ)^k

def nominalCompensation (Bs BD Bz : ℝ) (k : ℕ) (L G₀ c td : ℝ) (j : ℕ) : ℝ :=
  nominalWeight k (nominalJ Bs BD Bz k L G₀ c td) (Conclusion.stepGap BD Bz k L) j

theorem nominalCompensation_recurrence_scaled (Bs BD Bz : ℝ) {k j : ℕ} (hj : j<k)
    (L G₀ c td : ℝ) :
    (2:ℝ)^j*(nominalJ Bs BD Bz k L G₀ c td+
      ∑i∈Finset.Ico (j+1) k,nominalCompensation Bs BD Bz k L G₀ c td i) =
      (2:ℝ)^j*nominalCompensation Bs BD Bz k L G₀ c td j+Conclusion.stepGap BD Bz k L j :=
  nominalWeight_recurrence_scaled hj _ _

theorem nominalCompensation_total (Bs BD Bz : ℝ) (k : ℕ) (L G₀ c td : ℝ) :
    nominalJ Bs BD Bz k L G₀ c td+∑j∈Finset.range k,nominalCompensation Bs BD Bz k L G₀ c td j =
      Real.log (giantWindowScale ((2:ℝ)^(k+1)) G₀ L:ℝ)-2*c-2*td+Conclusion.initialGap Bs k L := by
  unfold nominalCompensation
  rw [nominalWeight_total]
  unfold nominalJ
  field_simp
  ring

end Ostmann.Construction

end

end OAI
