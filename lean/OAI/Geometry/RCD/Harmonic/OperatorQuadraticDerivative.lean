import OAI.Geometry.RCD.Coordinates.MatrixNormConversion
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi

namespace OAI

/-!
# Operator derivatives from finitely many quadratic tests

Polarization uses only the coordinate vectors and their pairwise sums.
This lets the scalar harmonic heat equations supply an operator equation,
and lets finitely many annular error estimates control every direction.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise

noncomputable section

namespace RegularPointCoordinates

variable {n : ℕ}

private def operatorEntries (A : Euclidean n →L[ℝ] Euclidean n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => A (EuclideanSpace.single j 1) i

private def matrixOperator : Matrix (Fin n) (Fin n) ℝ →L[ℝ]
    (Euclidean n →L[ℝ] Euclidean n) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap

private theorem matrixOperator_entries (A : Euclidean n →L[ℝ] Euclidean n) :
    matrixOperator (operatorEntries A) = A := by
  ext v i
  change (∑ j : Fin n, A (EuclideanSpace.single j 1) i * v j) = A v i
  have hv : v = ∑ j : Fin n, v j • EuclideanSpace.single j 1 := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
  have hAv : A v = ∑ j : Fin n, v j • A (EuclideanSpace.single j 1) := by
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul]
  rw [hAv]
  change _ = (WithLp.ofLp (∑ j, v j • A (EuclideanSpace.single j 1))) i
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The entry of a symmetric operator is obtained by real polarization. -/
theorem symmetric_entry_polarization (A : Euclidean n →L[ℝ] Euclidean n)
    (hA : A.IsSymmetric) (i j : Fin n) :
    A (EuclideanSpace.single j 1) i = (1 / 2 : ℝ) *
      (⟪EuclideanSpace.single i 1 + EuclideanSpace.single j 1,
          A (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)⟫_ℝ -
       ⟪EuclideanSpace.single i 1, A (EuclideanSpace.single i 1)⟫_ℝ -
       ⟪EuclideanSpace.single j 1, A (EuclideanSpace.single j 1)⟫_ℝ) := by
  let ei : Euclidean n := EuclideanSpace.single i 1
  let ej : Euclidean n := EuclideanSpace.single j 1
  have hs : ⟪ei, A ej⟫_ℝ = ⟪ej, A ei⟫_ℝ := by
    calc
      ⟪ei, A ej⟫_ℝ = ⟪A ei, ej⟫_ℝ := (hA ei ej).symm
      _ = ⟪ej, A ei⟫_ℝ := real_inner_comm _ _
  have he : ⟪ei, A ej⟫_ℝ = A (EuclideanSpace.single j 1) i := by
    simp only [ei, ej, EuclideanSpace.inner_single_left, conj_trivial, one_mul]
  change _ = (1 / 2 : ℝ) * (⟪ei + ej, A (ei + ej)⟫_ℝ - ⟪ei, A ei⟫_ℝ - ⟪ej, A ej⟫_ℝ)
  simp only [map_add, inner_add_left, inner_add_right, ← hs]
  linarith

private def polarizedMatrix (d : Euclidean n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (1 / 2 : ℝ) *
    (d (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) -
      d (EuclideanSpace.single i 1) - d (EuclideanSpace.single j 1))

/-- The operator formed by polarizing candidate quadratic derivatives. -/
def polarizedDerivative (d : Euclidean n → ℝ) : Euclidean n →L[ℝ] Euclidean n :=
  matrixOperator (polarizedMatrix d)

/-- Integrability of the finite polarization follows from its scalar tests. -/
theorem integrable_polarizedDerivative {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (d : X → Euclidean n → ℝ)
    (hs : ∀ i, MeasureTheory.Integrable (fun x => d x (EuclideanSpace.single i 1)) μ)
    (hp : ∀ i j, MeasureTheory.Integrable (fun x =>
      d x (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)) μ) :
    MeasureTheory.Integrable (fun x => polarizedDerivative (d x)) μ := by
  have hm : MeasureTheory.Integrable (fun x =>
      (fun i j : Fin n => (1 / 2 : ℝ) *
        (d x (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) -
          d x (EuclideanSpace.single i 1) - d x (EuclideanSpace.single j 1)))) μ := by
    apply MeasureTheory.Integrable.of_eval
    intro i
    apply MeasureTheory.Integrable.of_eval
    intro j
    exact (((hp i j).sub (hs i)).sub (hs j)).const_mul _
  exact (matrixOperator (n := n)).integrable_comp hm

/-- The finite polarization is symmetric, even before a quadratic identity is known. -/
theorem polarizedDerivative_isSymmetric (d : Euclidean n → ℝ) :
    (polarizedDerivative d).IsSymmetric := by
  change (Matrix.toEuclideanLin (polarizedMatrix d)).IsSymmetric
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  change (1 / 2 : ℝ) * (d (EuclideanSpace.single j 1 + EuclideanSpace.single i 1) -
    d (EuclideanSpace.single j 1) - d (EuclideanSpace.single i 1)) =
    (1 / 2 : ℝ) * (d (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) -
    d (EuclideanSpace.single i 1) - d (EuclideanSpace.single j 1))
  rw [add_comm (EuclideanSpace.single j 1)]
  ring

theorem polarizedDerivative_add (d e : Euclidean n → ℝ) :
    polarizedDerivative (fun v => d v + e v) = polarizedDerivative d + polarizedDerivative e := by
  have hm : polarizedMatrix (fun v => d v + e v) = polarizedMatrix d + polarizedMatrix e := by
    ext i j
    change (1 / 2 : ℝ) * ((_ + _) - (_ + _) - (_ + _)) = _
    dsimp [polarizedMatrix]
    ring
  exact (congrArg matrixOperator hm).trans (map_add matrixOperator _ _)

theorem polarizedDerivative_sub (d e : Euclidean n → ℝ) :
    polarizedDerivative (fun v => d v - e v) = polarizedDerivative d - polarizedDerivative e := by
  have hm : polarizedMatrix (fun v => d v - e v) = polarizedMatrix d - polarizedMatrix e := by
    ext i j
    change (1 / 2 : ℝ) * ((_ - _) - (_ - _) - (_ - _)) = _
    dsimp [polarizedMatrix]
    ring
  exact (congrArg matrixOperator hm).trans (map_sub matrixOperator _ _)

theorem polarizedDerivative_smul (a : ℝ) (d : Euclidean n → ℝ) :
    polarizedDerivative (fun v => a * d v) = a • polarizedDerivative d := by
  have hm : polarizedMatrix (fun v => a * d v) = a • polarizedMatrix d := by
    ext i j
    change (1 / 2 : ℝ) * (a * _ - a * _ - a * _) = a * _
    dsimp [polarizedMatrix]
    ring
  exact (congrArg matrixOperator hm).trans (map_smul matrixOperator a _)

/-- Polarization recovers an existing symmetric operator exactly. -/
theorem polarizedDerivative_quadratic_form (A : Euclidean n →L[ℝ] Euclidean n)
    (hA : A.IsSymmetric) : polarizedDerivative (fun v => ⟪v, A v⟫_ℝ) = A := by
  have hm : polarizedMatrix (fun v => ⟪v, A v⟫_ℝ) = operatorEntries A := by
    ext i j
    exact (symmetric_entry_polarization A hA i j).symm
  exact (congrArg matrixOperator hm).trans (matrixOperator_entries A)

/-- Only the coordinate vectors and their pairwise sums are needed for
a uniform bound on the polarized operator. -/
theorem polarizedDerivative_norm_le (d : Euclidean n → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsingle : ∀ i, |d (EuclideanSpace.single i 1)| ≤ ε)
    (hpair : ∀ i j, |d (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)| ≤ ε) :
    ‖polarizedDerivative d‖ ≤ (n : ℝ) ^ 2 * (3 / 2 * ε) := by
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) _‖ ≤ _
  apply matrix_euclidean_norm_le_of_entries _ (by positivity)
  intro i j
  change |(1 / 2 : ℝ) * (d (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) -
    d (EuclideanSpace.single i 1) - d (EuclideanSpace.single j 1))| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hh := abs_sub (d (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) -
    d (EuclideanSpace.single i 1)) (d (EuclideanSpace.single j 1))
  have hh' := abs_sub (d (EuclideanSpace.single i 1 + EuclideanSpace.single j 1))
    (d (EuclideanSpace.single i 1))
  have hi := hsingle i
  have hj := hsingle j
  have hij := hpair i j
  linarith

/-- Finitely many differentiable quadratic tests determine the derivative
of a symmetric operator-valued curve. -/
theorem hasDerivAt_operator_of_quadratic {Q : ℝ → (Euclidean n →L[ℝ] Euclidean n)}
    (hQ : ∀ t, (Q t).IsSymmetric) {t : ℝ} (d : Euclidean n → ℝ)
    (hd : ∀ v, HasDerivAt (fun s => ⟪v, Q s v⟫_ℝ) (d v) t) :
    HasDerivAt Q (polarizedDerivative d) t := by
  have he (i j : Fin n) : HasDerivAt (fun s => operatorEntries (Q s) i j)
      ((1 / 2 : ℝ) * (d (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) -
        d (EuclideanSpace.single i 1) - d (EuclideanSpace.single j 1))) t := by
    have hh := (((hd (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)).sub
      (hd (EuclideanSpace.single i 1))).sub (hd (EuclideanSpace.single j 1))).const_mul (1 / 2)
    apply hh.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s => symmetric_entry_polarization (Q s) (hQ s) i j
  have hm := hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (fun j => he i j))
  have h := (matrixOperator (n := n)).hasFDerivAt.comp_hasDerivAt t hm
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s => (matrixOperator_entries (Q s)).symm

/-- The resulting operator derivative agrees with all quadratic tests,
including directions that were not used in its finite construction. -/
theorem polarizedDerivative_quadratic {Q : ℝ → (Euclidean n →L[ℝ] Euclidean n)}
    (hQ : ∀ t, (Q t).IsSymmetric) {t : ℝ} (d : Euclidean n → ℝ)
    (hd : ∀ v, HasDerivAt (fun s => ⟪v, Q s v⟫_ℝ) (d v) t) (v : Euclidean n) :
    ⟪v, polarizedDerivative d v⟫_ℝ = d v := by
  have hD := hasDerivAt_operator_of_quadratic hQ d hd
  have hv := hD.clm_apply (hasDerivAt_const t v)
  have hinner := (hasDerivAt_const t v).inner ℝ hv
  simp only [inner_zero_left, map_zero, add_zero] at hinner
  exact hinner.unique (hd v)

end RegularPointCoordinates

end

end OAI
