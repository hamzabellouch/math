import Mathlib
import OAI.Computability.QuantumFactoring.OrderTrialFurther2

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Unnormalized joint amplitude after modular powering and the selected
phase-transform block. The modular-power register is NOT copied before this
interference sum. -/
noncomputable def selectedSampleAmplitude {G : Type*} [Group G]
    (Q k : ℕ) (a u : G) : ℂ := by
  classical
  exact (Q : ℂ)⁻¹ * ∑ x ∈ Finset.range Q,
    if a^x = u then phase ((k : ℝ)*x/Q) else 0

lemma selectedSampleAmplitude_residue {G : Type*} [Group G]
    (Q j : ℕ) (a : G) {t : ℕ} (ht : t < orderOf a) :
    selectedSampleAmplitude Q (bin Q (orderOf a) j) a (a^t) =
      residueAmplitude Q (orderOf a) j t := by
  classical
  unfold selectedSampleAmplitude residueAmplitude
  congr 1
  simp_rw [pow_inj_mod, Nat.mod_eq_of_lt ht]
  exact (Finset.sum_filter _ _).symm

lemma selectedSampleProbability_residue {G : Type*} [Group G]
    (Q j : ℕ) (a : G) {t : ℕ} (ht : t < orderOf a) :
    Complex.normSq (selectedSampleAmplitude Q (bin Q (orderOf a) j) a (a^t)) =
      residueProbability Q (orderOf a) j t := by
  rw [selectedSampleAmplitude_residue Q j a ht]
  exact Complex.normSq_eq_norm_sq _

/-- The literal modular-power verification in all three trial modes. -/
def ValidCandidate {G : Type*} [Group G] (B : ℕ) (a : G) (d : ℕ) : Prop :=
  1 ≤ d ∧ d < B ∧ a^d = 1

lemma ValidCandidate.order_dvd {G : Type*} [Group G] {B : ℕ} {a : G} {d : ℕ}
    (h : ValidCandidate B a d) : orderOf a ∣ d :=
  orderOf_dvd_of_pow_eq_one h.2.2

lemma trueOrder_valid {G : Type*} [Group G] [Finite G] {B : ℕ}
    (a : G) (hB : orderOf a < B) : ValidCandidate B a (orderOf a) :=
  ⟨orderOf_pos a, hB, pow_orderOf_eq_one a⟩

/-- Summing the exact per-reduced-label mass gives the prescribed true-order
probability phi(r) lambda(r), including r=1 and its label j=0. -/
lemma reduced_mass_sum {n Q B d : ℕ} (hB : 0 < B) (hd : 0 < d) :
    (∑ j ∈ (Finset.range d).filter (fun j => Nat.Coprime j d),
      (firstModeMass n Q B d j + secondModeMass n Q B d j +
        thirdModeMass n Q B d j)) =
      (Nat.totient d : ℝ) * (prescribedMass d : ℝ) := by
  classical
  have hm : ∀ j ∈ (Finset.range d).filter (fun j => Nat.Coprime j d),
      firstModeMass n Q B d j + secondModeMass n Q B d j + thirdModeMass n Q B d j =
        (prescribedMass d : ℝ) := by
    intro j hj
    exact three_mode_mass hB hd (Finset.mem_filter.mp hj).2
  rw [Finset.sum_congr rfl hm, Finset.sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  simp [Nat.totient, Nat.coprime_comm]

end ExactQuantumFactoring.OrderTrial


end

end OAI
