import OAI.NumberTheory.JointDickman.Probability.SymmetricSplitLaw
import OAI.NumberTheory.JointDickman.Amplification.RegularAmplificationMass

namespace OAI

/-! # Two independent sites with two fair splits at each site -/

namespace JointDickman

open Finset

structure TwoSiteSplit (P : Finset ℕ) where
  site₁ : P.powerset
  site₂ : P.powerset
  first₁ : P.powerset
  first₂ : P.powerset
  second₁ : P.powerset
  second₂ : P.powerset
  deriving Fintype, DecidableEq

noncomputable def twoSiteSplitMass (P : Finset ℕ) (x : TwoSiteSplit P) : ℝ :=
  bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) x.site₁.val *
  bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) x.site₂.val *
  subsetRetentionMass x.site₁.val x.first₁.val *
  subsetRetentionMass x.site₂.val x.first₂.val *
  subsetRetentionMass x.site₁.val x.second₁.val *
  subsetRetentionMass x.site₂.val x.second₂.val

def TwoSiteSplit.swap {P : Finset ℕ} (x : TwoSiteSplit P) : TwoSiteSplit P :=
  ⟨x.site₁, x.site₂, x.second₁, x.second₂, x.first₁, x.first₂⟩

theorem TwoSiteSplit.swap_swap {P : Finset ℕ} (x : TwoSiteSplit P) : x.swap.swap = x := by
  cases x
  rfl

def twoSiteSwapEquiv (P : Finset ℕ) : TwoSiteSplit P ≃ TwoSiteSplit P where
  toFun := TwoSiteSplit.swap
  invFun := TwoSiteSplit.swap
  left_inv := TwoSiteSplit.swap_swap
  right_inv := TwoSiteSplit.swap_swap

theorem twoSiteSplitMass_swap (P : Finset ℕ) (x : TwoSiteSplit P) :
    twoSiteSplitMass P x.swap = twoSiteSplitMass P x := by
  unfold twoSiteSplitMass TwoSiteSplit.swap
  ring

theorem subsetRetentionMass_nonneg (S T : Finset ℕ) : 0 ≤ subsetRetentionMass S T := by
  unfold subsetRetentionMass
  split_ifs <;> positivity

theorem twoSiteSplitMass_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : TwoSiteSplit P) :
    0 ≤ twoSiteSplitMass P x := by
  have hq : ∀ p ∈ P, 0 ≤ 1 / (p : ℝ) ∧ 1 / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  unfold twoSiteSplitMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (bernoulliSubsetMass_nonneg (mem_powerset.mp x.site₁.property) hq)
    (bernoulliSubsetMass_nonneg (mem_powerset.mp x.site₂.property) hq))
    (subsetRetentionMass_nonneg _ _)) (subsetRetentionMass_nonneg _ _))
    (subsetRetentionMass_nonneg _ _)) (subsetRetentionMass_nonneg _ _)

open Classical in
noncomputable def twoSiteSplitProbability (P : Finset ℕ) (E : TwoSiteSplit P → Prop) : ℝ :=
  ∑ x, if E x then twoSiteSplitMass P x else 0

theorem twoSiteSplitProbability_swap (P : Finset ℕ) (E : TwoSiteSplit P → Prop) :
    twoSiteSplitProbability P (fun x => E x.swap) = twoSiteSplitProbability P E := by
  classical
  unfold twoSiteSplitProbability
  have he := (twoSiteSwapEquiv P).sum_comp (fun x => if E x then twoSiteSplitMass P x else 0)
  convert he using 1
  apply sum_congr rfl
  intro x _
  change (if E x.swap then twoSiteSplitMass P x else 0) =
    if E x.swap then twoSiteSplitMass P x.swap else 0
  rw [twoSiteSplitMass_swap]

def amplificationSplitGood (B L T : ℕ) (τ C : ℝ) (S₁ S₂ A D : Finset ℕ) : Prop :=
  (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T ∧
    RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
    RegularPrimeSet B L τ C (S₁ \ A) ∧ RegularPrimeSet B L τ C (S₂ \ D)

def bothAmplificationSplitsGood (B L T : ℕ) (τ C : ℝ)
    (x : TwoSiteSplit (auxiliaryPrimes B)) : Prop :=
  amplificationSplitGood B L T τ C x.site₁.val x.site₂.val x.first₁.val x.first₂.val ∧
  amplificationSplitGood B L T τ C x.site₁.val x.site₂.val x.second₁.val x.second₂.val

theorem bothAmplificationSplitsGood_swap (B L T : ℕ) (τ C : ℝ)
    (x : TwoSiteSplit (auxiliaryPrimes B)) :
    bothAmplificationSplitsGood B L T τ C x.swap ↔ bothAmplificationSplitsGood B L T τ C x := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_comm

end JointDickman

end OAI
