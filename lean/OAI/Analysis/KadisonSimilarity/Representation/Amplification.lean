import OAI.Analysis.KadisonSimilarity.OperatorAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-!
# Matrix amplification and the main statements

Matrices act on finite Hilbert sums with their `ℓ²` norm. Consequently the
norm in `CommutatorEstimate` is the concrete operator matrix norm, rather than
the coordinatewise supremum norm of a matrix. No main estimate is assumed here.
-/

noncomputable section

universe u v

namespace KadisonSimilarity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hilbert direct sum of `n` copies of `H`. -/
abbrev HilbertCopies (H : Type u) (n : ℕ) := PiLp 2 (fun _ : Fin n => H)

/-- An operator matrix acts by matrix-vector multiplication on the Hilbert sum. -/
def matrixOperator {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j : Fin n, (X i j).comp (PiLp.proj 2 (fun _ : Fin n => H) j))

@[simp] theorem matrixOperator_apply {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (ξ : HilbertCopies H n) (i : Fin n) :
    matrixOperator X ξ i = ∑ j : Fin n, X i j (ξ j) := by
  simp [matrixOperator]

/-- The diagonal amplification of one operator. -/
def amplify (Y : H →L[ℂ] H) (n : ℕ) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Y.comp (PiLp.proj 2 (fun _ : Fin n => H) i))

@[simp] theorem amplify_apply (Y : H →L[ℂ] H) (n : ℕ)
    (ξ : HilbertCopies H n) (i : Fin n) : amplify Y n ξ i = Y (ξ i) := by
  simp [amplify]

/-- Hilbert amplification does not increase the operator norm. -/
theorem norm_amplify_le (Y : H →L[ℂ] H) (n : ℕ) : ‖amplify Y n‖ ≤ ‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
  intro ξ
  have hs : ‖amplify Y n ξ‖ ^ 2 ≤ (‖Y‖ * ‖ξ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i : Fin n, ‖amplify Y n ξ i‖ ^ 2 ≤
          ∑ i : Fin n, (‖Y‖ * ‖ξ i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [amplify_apply]
        exact pow_le_pow_left₀ (norm_nonneg _) (Y.le_opNorm _) 2
      _ = ‖Y‖ ^ 2 * (∑ i : Fin n, ‖ξ i‖ ^ 2) := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ = (‖Y‖ * ‖ξ‖) ^ 2 := by rw [← PiLp.norm_sq_eq_of_L2]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Y) (norm_nonneg ξ))).mp hs

/-- Positive finite amplification preserves the operator norm. -/
theorem norm_amplify (Y : H →L[ℂ] H) {n : ℕ} (hn : 0 < n) :
    ‖amplify Y n‖ = ‖Y‖ := by
  apply le_antisymm (norm_amplify_le Y n)
  apply ContinuousLinearMap.opNorm_le_bound Y (norm_nonneg (amplify Y n))
  intro ξ
  let i : Fin n := ⟨0, hn⟩
  have hmap : amplify Y n (PiLp.single 2 i ξ) = PiLp.single 2 i (Y ξ) := by
    ext j
    by_cases h : j = i
    · subst j
      simp only [amplify_apply, PiLp.single_eq_same]
    · simp only [amplify_apply, PiLp.single_apply, ite_eq_right h, map_zero]
  have hnorm := (amplify Y n).le_opNorm (PiLp.single 2 i ξ)
  simpa only [hmap, PiLp.norm_single] using hnorm

/-- Matrix amplification of an inner derivation agrees with the commutator
of the amplified operator and the matrix operator. -/
theorem commutator_amplify_matrixOperator (Y : H →L[ℂ] H) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    commutator (amplify Y n) (matrixOperator X) =
      matrixOperator (fun i j => commutator Y (X i j)) := by
  ext ξ i
  simp [commutator, matrixOperator, amplify, map_sum, Finset.sum_sub_distrib]

/-- Inner derivation on the full bounded-operator algebra. -/
def innerDerivation (Y : H →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ContinuousLinearMap.mul ℂ (H →L[ℂ] H) Y -
    (ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip Y

@[simp] theorem innerDerivation_apply (Y T : H →L[ℂ] H) :
    innerDerivation Y T = commutator Y T := rfl

variable [CompleteSpace H]

/-- The scalar commutator seminorm `g_P(Y)`, expressed as the norm of the
bounded linear map `a ↦ Ya - aY` on the represented algebra. -/
def scalarCommutatorNorm (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) : ℝ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  exact ‖(innerDerivation Y).comp P.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL‖

theorem scalarCommutatorNorm_nonneg (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    0 ≤ scalarCommutatorNorm P Y := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  exact norm_nonneg ((innerDerivation Y).comp
    P.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL)

/-- The defining operator norm controls every scalar commutator. -/
theorem norm_commutator_le_scalarCommutatorNorm (P : VonNeumannAlgebra H)
    (Y T : H →L[ℂ] H) (hT : T ∈ P) :
    ‖commutator Y T‖ ≤ scalarCommutatorNorm P Y * ‖T‖ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  exact ((innerDerivation Y).comp
    P.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL).le_opNorm ⟨T, hT⟩

/-- Characterization of the scalar commutator norm by homogeneous bounds. -/
theorem scalarCommutatorNorm_le_iff (P : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c) :
    scalarCommutatorNorm P Y ≤ c ↔
      ∀ T : H →L[ℂ] H, T ∈ P → ‖commutator Y T‖ ≤ c * ‖T‖ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  constructor
  · intro h T hT
    exact (norm_commutator_le_scalarCommutatorNorm P Y T hT).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg T))
  · intro h
    apply ContinuousLinearMap.opNorm_le_bound _ hc
    intro a
    exact h a a.property

/-- The scalar seminorm is finite with the elementary commutator bound. -/
theorem scalarCommutatorNorm_le (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    scalarCommutatorNorm P Y ≤ 2 * ‖Y‖ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  exact norm_commutator_le Y (a : H →L[ℂ] H)

/-- The averaging perturbation estimate for the scalar commutator seminorm. -/
theorem scalarCommutatorNorm_perturb (P : VonNeumannAlgebra H)
    (Y Z : H →L[ℂ] H) :
    scalarCommutatorNorm P Y ≤ scalarCommutatorNorm P Z + 2 * ‖Y - Z‖ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have := scalarCommutatorNorm_nonneg P Z
    positivity)
  intro a
  change ‖commutator Y (a : H →L[ℂ] H)‖ ≤ _
  calc
    _ ≤ scalarCommutatorNorm P Z * ‖(a : H →L[ℂ] H)‖ +
        2 * ‖Y - Z‖ * ‖(a : H →L[ℂ] H)‖ :=
      norm_commutator_le_of_approx Y Z a
        (norm_commutator_le_scalarCommutatorNorm P Z a a.property) le_rfl
    _ = _ := by change _ = _ * ‖(a : H →L[ℂ] H)‖; ring

/-- The fixed-algebra conclusion of the manuscript's uniform estimate. -/
def CommutatorEstimate (P : VonNeumannAlgebra H) (C : ℝ) : Prop :=
  ∀ (Y : H →L[ℂ] H) (n : ℕ) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)),
    (∀ i j, X i j ∈ P) →
    ‖commutator (amplify Y n) (matrixOperator X)‖ ≤
      C * scalarCommutatorNorm P Y * ‖matrixOperator X‖

/-- The exact universal quantifiers of Theorem `thm:universal`. -/
def UniformCommutatorEstimate (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : VonNeumannAlgebra K), CommutatorEstimate P C

/-- The existence of a single numerical constant in Theorem `thm:universal`. -/
def UniversalCommutatorTheorem : Prop := ∃ C : ℝ, 0 ≤ C ∧ UniformCommutatorEstimate.{u} C

/-- The exact unrestricted similarity statement, Theorem `thm:similarity`. -/
def SimilarityTheorem : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (K : Type v) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (π : BoundedUnitalHom A K),
    SimilarToStar A K π

/-- The projections indexing the usual off-diagonal distance seminorm. -/
abbrev CommutantProjection (M : VonNeumannAlgebra H) :=
  {e : H →L[ℂ] H // e ∈ M.commutant ∧ star e = e ∧ e * e = e}

/-- The off-diagonal distance seminorm from Corollary `cor:hyperreflexivity`. -/
def offDiagonalSeminorm (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) : ℝ :=
  sSup (Set.range fun e : CommutantProjection M =>
    ‖(1 - (e : H →L[ℂ] H)) * T * (e : H →L[ℂ] H)‖)

/-- Orthogonal projections are contractions, including the zero projection. -/
theorem norm_projection_le_one (e : H →L[ℂ] H) (hstar : star e = e)
    (hsq : e * e = e) : ‖e‖ ≤ 1 := by
  have hnorm : ‖e‖ * ‖e‖ = ‖e‖ := by
    rw [← CStarRing.norm_star_mul_self, hstar, hsq]
  nlinarith [norm_nonneg e]

theorem norm_one_sub_projection_le_one (e : H →L[ℂ] H) (hstar : star e = e)
    (hsq : e * e = e) : ‖1 - e‖ ≤ 1 := by
  apply norm_projection_le_one
  · simp [hstar]
  · calc
      (1 - e) * (1 - e) = 1 - e - e + e * e := by noncomm_ring
      _ = 1 - e := by rw [hsq]; abel

/-- The off-diagonal supremum is bounded by the operator norm. -/
theorem offDiagonalSeminorm_le (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    offDiagonalSeminorm M T ≤ ‖T‖ := by
  let e₀ : CommutantProjection M := ⟨0, by simp⟩
  unfold offDiagonalSeminorm
  apply csSup_le
  · exact ⟨_, ⟨e₀, rfl⟩⟩
  · rintro r ⟨e, rfl⟩
    have he : ‖e.val‖ ≤ 1 := norm_projection_le_one e.val e.property.2.1 e.property.2.2
    have he' : ‖1 - e.val‖ ≤ 1 :=
      norm_one_sub_projection_le_one e.val e.property.2.1 e.property.2.2
    calc
      ‖(1 - e.val) * T * e.val‖ ≤ (‖1 - e.val‖ * ‖T‖) * ‖e.val‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg e.val))
      _ ≤ (1 * ‖T‖) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right he' (norm_nonneg T)) he
          (norm_nonneg e.val) (by positivity)
      _ = ‖T‖ := by ring

/-- The quantitative conclusion of Corollary `cor:hyperreflexivity`, with the
same constant as the universal commutator theorem. -/
def UniversalHyperreflexivity (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra K) (T : K →L[ℂ] K),
    Metric.infDist T (M : Set (K →L[ℂ] K)) ≤ 2 * C * offDiagonalSeminorm M T

end KadisonSimilarity

end

end OAI
