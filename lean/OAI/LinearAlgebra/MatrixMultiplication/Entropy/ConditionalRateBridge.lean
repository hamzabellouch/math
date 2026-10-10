import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.ConditionalLabels

open MatrixMultiplication.Foundation Filter StageHierarchyResources HierarchySeparationRates
open LabelHierarchyCounts
open scoped BigOperators Topology Classical

universe u v
variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

def normalizedCountLaw (counts : A → ℕ) (hD : 0 < ∑ a, counts a) : FiniteLaw A where
  mass a := (counts a : ℝ) / (∑ b, counts b : ℕ)
  nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  total := by
    rw [← Finset.sum_div, ← Nat.cast_sum]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD))

@[simp] theorem normalizedCountLaw_mass (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (a : A) :
    (normalizedCountLaw counts hD).mass a =
      (counts a : ℝ) / (∑ b, counts b : ℕ) := rfl

theorem normalized_prefix_mass (counts : A → ℕ) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (n : ℕ) (r : LabelRecord Label n) :
    (p.map (labelRecordOf labels n)).mass r =
      (sourcePrefixCounts counts labels n r : ℝ) / (∑ a, counts a : ℕ) := by
  simp only [FiniteLaw.map_mass, mass, sourcePrefixCounts, pushforwardCounts,
    Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : labelRecordOf labels n a = r <;> simp [h]

theorem zero_prefix_contribution_of_count_eq_zero (counts : A → ℕ) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (n : ℕ) (r : LabelRecord Label n)
    (hzero : sourcePrefixCounts counts labels n r = 0) :
    (p.map (labelRecordOf labels n)).mass r *
      finiteEntropy ((p.conditional (labelRecordOf labels n) r).map (labels n)).mass = 0 := by
  rw [normalized_prefix_mass counts p mass labels n r, hzero,
    Nat.cast_zero, zero_div, zero_mul]

theorem tendsto_log_prefix_multinomial (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log
      (Nat.multinomial Finset.univ
        (sourcePrefixCounts (fun a => t * counts a) labels n) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy (p.map (labelRecordOf labels n)).mass)) := by
  have hsum : (∑ r, sourcePrefixCounts counts labels n r) = ∑ a, counts a :=
    pushforwardCounts_sum counts (labelRecordOf labels n)
  have hpositive : 0 < ∑ r, sourcePrefixCounts counts labels n r := by rwa [hsum]
  have hmass : (fun r => (sourcePrefixCounts counts labels n r : ℝ) /
      (∑ r, sourcePrefixCounts counts labels n r : ℕ)) =
      (p.map (labelRecordOf labels n)).mass := by
    funext r
    rw [hsum]
    exact (normalized_prefix_mass counts p mass labels n r).symm
  have h := tendsto_log_multinomial_mul (sourcePrefixCounts counts labels n) hpositive
  rw [hmass, hsum] at h
  have hscale (t : ℕ) : sourcePrefixCounts (fun a => t * counts a) labels n =
      (fun r => t * sourcePrefixCounts counts labels n r) :=
    funext (sourcePrefixCounts_mul counts labels t n)
  simpa only [hscale] using h

theorem stageEntropyRate_div_eq_refinementEntropy (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (depth n : ℕ) (hn : n < depth) :
    stageEntropyRate counts labels n / (∑ a, counts a : ℕ) =
      (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n := by
  have hstage := (tendsto_log_stageRefinementCount_div counts labels n).div_const
    ((∑ a, counts a : ℕ) : ℝ)
  simp only [div_div] at hstage
  have hcoarse := tendsto_log_prefix_multinomial counts hD p mass labels n
  have hfine := tendsto_log_prefix_multinomial counts hD p mass labels (n + 1)
  have heq : finiteEntropy (p.map (labelRecordOf labels (n + 1))).mass =
      finiteEntropy (p.map (labelRecordOf labels n)).mass +
        stageEntropyRate counts labels n / (∑ a, counts a : ℕ) := by
    apply tendsto_nhds_unique hfine
    apply (hcoarse.add hstage).congr
    intro t
    rw [multinomial_succ (sourcePrefixCounts (fun a => t * counts a) labels) n
      (sourcePrefixCounts_compatible (fun a => t * counts a) labels n)]
    have hcoarse_pos : 0 < Nat.multinomial Finset.univ
        (sourcePrefixCounts (fun a => t * counts a) labels n) := Nat.multinomial_pos _ _
    have hrefinement_pos : 0 <
        refinementCount (sourcePrefixCounts (fun a => t * counts a) labels) n :=
      stageRefinementCount_pos counts labels n t
    rw [Nat.cast_mul, Real.log_mul
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcoarse_pos))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hrefinement_pos)), add_div]
    rfl
  have hchain := (FiniteLabelHierarchy.ofLawLabels p labels depth).prefixLaw_entropy_succ
    n (Nat.succ_le_of_lt hn)
  rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass,
    FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass] at hchain
  linarith

theorem stagePairingRate_div_eq_lawPairingRate (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    stagePairingRate counts labels depth reader pair / (∑ a, counts a : ℕ) =
      lawPairingRate p labels depth reader pair := by
  unfold stagePairingRate lawPairingRate pairingRate
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : reader n = pair
  · simp only [h, ite_true]
    exact stageEntropyRate_div_eq_refinementEntropy counts hD p mass labels depth n.val n.isLt
  · simp [h]

theorem tendsto_log_stagePairingSize_law (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p labels depth reader pair)) := by
  rw [← stagePairingRate_div_eq_lawPairingRate counts hD p mass labels depth reader pair]
  exact tendsto_log_stagePairingSize_normalized counts labels depth reader pair

theorem stageEntropyRate_div_eq_normalizedCountLaw_refinementEntropy
    (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth n : ℕ) (hn : n < depth) :
    stageEntropyRate counts labels n / (∑ a, counts a : ℕ) =
      (FiniteLabelHierarchy.ofLawLabels (normalizedCountLaw counts hD)
        labels depth).refinementEntropy n :=
  stageEntropyRate_div_eq_refinementEntropy counts hD (normalizedCountLaw counts hD)
    (fun _ => rfl) labels depth n hn

theorem tendsto_log_stagePairingSize_normalizedCountLaw
    (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate (normalizedCountLaw counts hD) labels depth reader pair)) :=
  tendsto_log_stagePairingSize_law counts hD (normalizedCountLaw counts hD)
    (fun _ => rfl) labels depth reader pair

end MatrixMultiplication.ConditionalLabels

end

end OAI
