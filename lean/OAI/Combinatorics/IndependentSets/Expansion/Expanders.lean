import Mathlib
import OAI.Combinatorics.IndependentSets.Fourier.Walsh2
import OAI.Combinatorics.IndependentSets.Expansion.CayleyTailCount
import OAI.Combinatorics.IndependentSets.Expansion.CayleySpectral

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.Expanders

open scoped BigOperators
open IndependentSetsGames.Foundations.Hastad
open CayleySpectral

abbrev Generators (n m : Nat) := Fin (4 * m) → Cube (Fin n)

def badFrequency {n m : Nat} (g : Generators n m) (s : Cube (Fin n)) : ℝ :=
  if s = zeroFrequency then 0 else
    if CayleyTailCount.badWord m (fun d => AssignmentTester.parity s (g d)) then 1 else 0

def badMass {n m : Nat} (g : Generators n m) : ℝ :=
  ∑ s : Cube (Fin n), badFrequency g s

theorem badFrequency_nonnegative {n m : Nat}
    (g : Generators n m) (s : Cube (Fin n)) : 0 ≤ badFrequency g s := by
  unfold badFrequency
  split_ifs <;> norm_num

theorem mean_badFrequency_le {n m : Nat} (s : Cube (Fin n)) :
    (𝔼 g : Generators n m, badFrequency g s) ≤ 2 * (2 / 3 : ℝ) ^ m := by
  classical
  by_cases hs : s = zeroFrequency
  · simp only [badFrequency, ite_eq_left hs, Finset.expect_const_zero]
    positivity
  · have hs' : s ≠ (fun _ => false) := hs
    simp only [badFrequency, ite_eq_right hs]
    rw [CayleySampling.expect_parity_samples s hs'
      (fun w : Fin (4 * m) → Bool => if CayleyTailCount.badWord m w then (1 : ℝ) else 0)]
    exact CayleyTailCount.twoTail_probability m (by simp)

theorem mean_badMass_le (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    (𝔼 g : Generators n m, badMass g) ≤ 1 / 2 := by
  calc
    _ = ∑ s : Cube (Fin n), 𝔼 g : Generators n m, badFrequency g s := by
      unfold badMass
      rw [Finset.expect_sum_comm]
    _ ≤ ∑ _s : Cube (Fin n), 2 * (2 / 3 : ℝ) ^ m :=
      Finset.sum_le_sum (fun s _ => mean_badFrequency_le s)
    _ = (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) := by
      simp [Cube]
    _ ≤ 1 / 2 := CayleyTailCount.union_bound_le_half n m hm

theorem exists_generators (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    ∃ g : Generators n m, ∀ s : Cube (Fin n),
      s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ) := by
  classical
  have hmpos : 0 < m := by omega
  let : Nonempty (Fin (4 * m)) := ⟨⟨0, by omega⟩⟩
  have havg : (𝔼 g : Generators n m, badMass g) < (1 : ℝ) :=
    lt_of_le_of_lt (mean_badMass_le n m hm) (by norm_num)
  obtain ⟨g, _, hg⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty havg
  refine ⟨g, fun s hs => ?_⟩
  have hgood : ¬ CayleyTailCount.badWord m
      (fun d => AssignmentTester.parity s (g d)) := by
    intro hbad
    have hsingle : badFrequency g s ≤ badMass g :=
      Finset.single_le_sum (fun t _ => badFrequency_nonnegative g t) (Finset.mem_univ s)
    simp only [badFrequency, ite_eq_right hs, ite_eq_left hbad] at hsingle
    exact (not_le_of_gt hg) hsingle
  unfold eigenvalue
  simp_rw [← AssignmentTester.bitSign_parity]
  exact CayleyTailCount.not_badWord_bias m (by simp) hmpos _ hgood

def baseDimension : Nat := 448
def initialDegree : Nat := 2 ^ 16
def initialQuarterDegree : Nat := 2 ^ 14
def basePower : Nat := 7

theorem base_arithmetic :
    4 * initialQuarterDegree = initialDegree ∧
    3 * (baseDimension + 2) ≤ initialQuarterDegree ∧
    (2 : Nat) ^ baseDimension = (initialDegree ^ basePower) ^ 4 ∧
    (1 / 2 : ℝ) ^ basePower ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [initialDegree, initialQuarterDegree]
  · norm_num [baseDimension, initialQuarterDegree]
  · simpa only [baseDimension, initialDegree, basePower] using CayleyTailCount.seventh_power_size
  · norm_num [basePower]

theorem exists_initial_generators :
    ∃ g : Generators baseDimension initialQuarterDegree,
      ∀ s : Cube (Fin baseDimension), s ≠ zeroFrequency →
        |eigenvalue g s| ≤ (1 / 2 : ℝ) :=
  exists_generators _ _ base_arithmetic.2.1

abbrev BaseVertex := Cube (Fin baseDimension)
abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)
def baseDegree : Nat := initialDegree ^ basePower

theorem card_basePort : Fintype.card BasePort = baseDegree := by
  simp only [BasePort, Fintype.card_fun, Fintype.card_fin]
  rw [base_arithmetic.1]
  rfl

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

theorem exists_baseGraph :
    ∃ H : PoweringWalks.PortGraph BaseVertex BasePort,
      SpectralReturn.SpectralCertificate H (1 / 100 : ℝ) := by
  obtain ⟨g, hg⟩ := exists_initial_generators
  refine ⟨cayleyGraph (powerGenerators g basePower), ?_⟩
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact (power_eigenvalue_bound g (1 / 2) (by norm_num) hg basePower s hs).trans
      base_arithmetic.2.2.2

end IndependentSetsGames.Foundations.PCP.Expanders
end
namespace IndependentSetsGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]

end IndependentSetsGames.Foundations.PCP.GraphTransport

end OAI
