import OAI.NumberTheory.EgyptianFractions.GeometricRawDensity

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337.GeometricDensity

/-- Combine the deterministic and sampled lists according to the level cutoff.
The index set is kept fixed, so repeated sampled products retain their full
multiplicity. The same choice also changes the auxiliary factor from `C` to `1`.
The shifted moment input is uniform over all positive divisors of the common
denominator; no moment assumption about the chosen list is added. -/
def residueData_of_two_lists
    {DM D₀ η c r S loss : ℝ} {C M : ℕ}
    (I : Finset ℕ) (hI : I.Nonempty) (t₀ t₁ : ℕ → ℕ)
    (hpos₀ : ∀ i ∈ I, 0 < t₀ i) (hpos₁ : ∀ i ∈ I, 0 < t₁ i)
    (hdvd₀ : ∀ i ∈ I, t₀ i ∣ M) (hdvd₁ : ∀ i ∈ I, t₁ i ∣ M)
    (E₀ E₁ : ℕ → Finset ℕ)
    (hcount₀ : ∀ j < depth DM η S, Real.exp S < cutoff DM η S j →
      ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊, u ∉ E₀ j →
        cutoff DM η S (j + 1) < (u : ℝ) →
        contraction η S * (I.card : ℝ) / loss ≤
          ((I.filter (fun i => Int.fract (-((C * t₀ i : ℕ) : ℝ) / u) <
            contraction η S)).card : ℝ))
    (hcount₁ : ∀ j < depth DM η S, cutoff DM η S j ≤ Real.exp S →
      ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊, u ∉ E₁ j →
        cutoff DM η S (j + 1) < (u : ℝ) →
        contraction η S * (I.card : ℝ) / loss ≤
          ((I.filter (fun i => Int.fract (-(t₁ i : ℝ) / u) <
            contraction η S)).card : ℝ))
    (herror₀ : ∀ j < depth DM η S, Real.exp S < cutoff DM η S j →
      ((E₀ j).card : ℝ) ≤ cutoff DM η S j * Real.exp (-c * ResidueLevels.scale S))
    (herror₁ : ∀ j < depth DM η S, cutoff DM η S j ≤ Real.exp S →
      ((E₁ j).card : ℝ) ≤ cutoff DM η S j * Real.exp (-c * ResidueLevels.scale S))
    (hmoment : ∀ j < depth DM η S, ∀ t : ℕ, 0 < t → t ∣ M →
      (∑ h ∈ Finset.Icc 1 ⌊cutoff DM η S (j + 1)⌋₊,
        densityDivisorCount (cutoff DM η S j) (factor DM η S C j * t + h) ^ r) ≤
          cutoff DM η S (j + 1) * Real.exp (S ^ (1 / 4 : ℝ)))
    (hterminal : ∀ u : ℕ, (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) →
      S ^ D₀ < (u : ℝ) → ∃ t : ℕ, 0 < t ∧ t ∣ M ∧
        Int.fract (-(t : ℝ) / u) < (u : ℝ) ^ (-η)) :
    NormalizedResidueData DM D₀ η c r S loss C M := by
  classical
  let t : ℕ → ℕ → ℕ := fun j i =>
    if Real.exp S < cutoff DM η S j then t₀ i else t₁ i
  let E : ℕ → Finset ℕ := fun j =>
    if Real.exp S < cutoff DM η S j then E₀ j else E₁ j
  have hpos (j i : ℕ) (hi : i ∈ I) : 0 < t j i := by
    dsimp [t]
    split_ifs <;> first | exact hpos₀ i hi | exact hpos₁ i hi
  have hdvd (j i : ℕ) (hi : i ∈ I) : t j i ∣ M := by
    dsimp [t]
    split_ifs <;> first | exact hdvd₀ i hi | exact hdvd₁ i hi
  refine {
    indices := fun _ => I
    divisor := t
    exceptional := E
    indices_nonempty := fun _ _ => hI
    divisor_pos := fun j _ i hi => hpos j i hi
    divisor_dvd := fun j _ i hi => hdvd j i hi
    many_residues := ?_
    exception_bound := ?_
    moment_bound := fun j hj i hi => hmoment j hj (t j i) (hpos j i hi) (hdvd j i hi)
    terminal_residue := hterminal }
  · intro j hj u hu huE hunext
    by_cases hhigh : Real.exp S < cutoff DM η S j
    · have hnot : u ∉ E₀ j := by simpa only [E, ite_eq_left hhigh] using huE
      simpa only [t, ite_eq_left hhigh, factor, ResidueLevels.factor] using
        hcount₀ j hj hhigh u hu hnot hunext
    · have hnot : u ∉ E₁ j := by simpa only [E, ite_eq_right hhigh] using huE
      simpa only [t, ite_eq_right hhigh, factor, ResidueLevels.factor, one_mul] using
        hcount₁ j hj (le_of_not_gt hhigh) u hu hnot hunext
  · intro j hj
    by_cases hhigh : Real.exp S < cutoff DM η S j
    · simpa only [E, ite_eq_left hhigh] using herror₀ j hj hhigh
    · simpa only [E, ite_eq_right hhigh] using herror₁ j hj (le_of_not_gt hhigh)

end Problem337.GeometricDensity

end

end OAI
