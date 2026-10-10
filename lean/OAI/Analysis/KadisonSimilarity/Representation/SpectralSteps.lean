import OAI.Analysis.KadisonSimilarity.Representation.ProjectionCommutators
import OAI.Analysis.KadisonSimilarity.Hyperreflexivity

namespace OAI

/-!
# The spectral-step part of the hyperreflexivity deduction

`SpectralStepApproximation` isolates exactly the norm approximation by spectral
projections that the manuscript uses. It is the step-function specialization of
Blackadar, *Operator Algebras* (2006; revised manuscript February 8, 2017),
I.6.1.3--4, with membership of spectral projections from I.9.2.1(iv).
The scalar offset is essential: summation by parts gives a total variation of
the remaining coefficients at most twice the operator norm.

The spectral approximation and the uniform commutator estimate together imply
the hyperreflexivity bound.
-/

noncomputable section

namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A scalar offset plus a finite linear combination of spectral projections. -/
def spectralStep {n : ℕ} (r : ℝ) (c : Fin n → ℝ) (e : Fin n → H →L[ℂ] H) :
    H →L[ℂ] H := (r : ℂ) • 1 + ∑ i, (c i : ℂ) • e i

/-- Spectral approximation with a bound on the sum of absolute coefficients. -/
def SpectralStepApproximation (P : VonNeumannAlgebra H) : Prop :=
  ∀ A : H →L[ℂ] H, A ∈ P → star A = A → ∀ δ : ℝ, 0 < δ →
    ∃ (n : ℕ) (r : ℝ) (c : Fin n → ℝ) (e : Fin n → H →L[ℂ] H),
      (∀ i, e i ∈ P ∧ star (e i) = e i ∧ e i * e i = e i) ∧
      (∑ i, |c i|) ≤ 2 * ‖A‖ ∧ ‖A - spectralStep r c e‖ ≤ δ

omit [CompleteSpace H] in
/-- The scalar term has zero commutator; the other terms retain their coefficients. -/
theorem commutator_spectralStep (T : H →L[ℂ] H) {n : ℕ}
    (r : ℝ) (c : Fin n → ℝ) (e : Fin n → H →L[ℂ] H) :
    commutator T (spectralStep r c e) = ∑ i, (c i : ℂ) • commutator T (e i) := by
  change innerDerivation T (spectralStep r c e) = _
  simp [spectralStep, map_add, map_sum, innerDerivation_apply, commutator]

/-- A finite spectral sum is controlled by the total variation of its coefficients. -/
theorem norm_commutator_spectralStep_le (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    {n : ℕ} (r : ℝ) (c : Fin n → ℝ) (e : Fin n → H →L[ℂ] H)
    (he : ∀ i, e i ∈ M.commutant ∧ star (e i) = e i ∧ e i * e i = e i) :
    ‖commutator T (spectralStep r c e)‖ ≤
      (∑ i, |c i|) * offDiagonalSeminorm M T := by
  rw [commutator_spectralStep]
  calc
    ‖∑ i, (c i : ℂ) • commutator T (e i)‖ ≤
        ∑ i, ‖(c i : ℂ) • commutator T (e i)‖ := norm_sum_le _ _
    _ = ∑ i, |c i| * ‖commutator T (e i)‖ := by simp [norm_smul]
    _ ≤ ∑ i, |c i| * offDiagonalSeminorm M T := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (norm_commutator_projection_le_offDiagonal M T ⟨e i, he i⟩) (abs_nonneg _)
    _ = (∑ i, |c i|) * offDiagonalSeminorm M T := by rw [Finset.sum_mul]

/-- The projection approximation yields the claimed sharp scalar-level factor
`2` for a selfadjoint input. -/
theorem norm_commutator_selfAdjoint_of_spectralSteps (M : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation M.commutant) (T A : H →L[ℂ] H)
    (hA : A ∈ M.commutant) (hAstar : star A = A) :
    ‖commutator T A‖ ≤ 2 * offDiagonalSeminorm M T * ‖A‖ := by
  have hα := offDiagonalSeminorm_nonneg M T
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (2 * ‖T‖ + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n, r, c, e, he, hc, herr⟩ := approximation A hA hAstar δ hδ
  have hstep := norm_commutator_spectralStep_le M T r c e he
  have hclose : ‖commutator T A - commutator T (spectralStep r c e)‖ ≤ 2 * ‖T‖ * δ := by
    have heq : commutator T A - commutator T (spectralStep r c e) =
        commutator T (A - spectralStep r c e) := by
      change innerDerivation T A - innerDerivation T (spectralStep r c e) =
        innerDerivation T (A - spectralStep r c e)
      exact (map_sub _ _ _).symm
    rw [heq]
    exact (norm_commutator_le _ _).trans (mul_le_mul_of_nonneg_left herr (by positivity))
  have hδε : 2 * ‖T‖ * δ ≤ ε := by
    have hden : 0 < 2 * ‖T‖ + 1 := by positivity
    dsimp [δ]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  calc
    ‖commutator T A‖ ≤ ‖commutator T (spectralStep r c e)‖ +
        ‖commutator T A - commutator T (spectralStep r c e)‖ := norm_le_insert' _ _
    _ ≤ (2 * ‖A‖) * offDiagonalSeminorm M T + 2 * ‖T‖ * δ :=
      add_le_add (hstep.trans (mul_le_mul_of_nonneg_right hc hα)) hclose
    _ ≤ 2 * offDiagonalSeminorm M T * ‖A‖ + ε := by nlinarith

/-- The real/imaginary decomposition now yields the scalar factor `4`. -/
theorem scalarCommutatorNorm_le_four_of_spectralSteps (M : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation M.commutant) (T : H →L[ℂ] H) :
    scalarCommutatorNorm M.commutant T ≤ 4 * offDiagonalSeminorm M T := by
  apply scalarCommutatorNorm_le_four_of_selfAdjoint M T
  intro A hA hAstar
  exact norm_commutator_selfAdjoint_of_spectralSteps M approximation T A hA hAstar

/-- Spectral approximation and the uniform commutator estimate imply the
hyperreflexivity bound with constant `2 * C`. -/
theorem hyperreflexivity_of_spectralSteps_and_arveson (M : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation M.commutant) (T : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (arveson : ArvesonDistanceFormula M T)
    (estimate : CommutatorEstimate M.commutant C) :
    Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ 2 * C * offDiagonalSeminorm M T :=
  hyperreflexivity_bound_of_arveson M T hC arveson estimate
    (scalarCommutatorNorm_le_four_of_spectralSteps M approximation T)

end KadisonSimilarity

end

end OAI
