import Mathlib

namespace OAI

noncomputable section

namespace KadisonSimilarity

universe u v

section Homomorphisms

variable (A H : Type*) [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev BoundedUnitalHom :=
  {π : A →ₐ[ℂ] (H →L[ℂ] H) // Continuous π}

def SimilarToStar (π : BoundedUnitalHom A H) : Prop :=
  ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
    (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))

end Homomorphisms

section Commutators

variable {R : Type*} [NormedRing R]

def commutator (S T : R) : R := S * T - T * S

end Commutators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section

attribute [-instance] NonUnitalCStarAlgebra.toNormedSpace

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

abbrev HilbertCopies (H : Type u) (n : ℕ) := PiLp 2 (fun _ : Fin n => H)

def matrixOperator {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j : Fin n, (X i j).comp (PiLp.proj 2 (fun _ : Fin n => H) j))

def amplify (Y : H →L[ℂ] H) (n : ℕ) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Y.comp (PiLp.proj 2 (fun _ : Fin n => H) i))

def innerDerivation (Y : H →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ContinuousLinearMap.mul ℂ (H →L[ℂ] H) Y -
    (ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip Y

variable [CompleteSpace H]

def scalarCommutatorNorm (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) : ℝ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  exact ‖(innerDerivation Y).comp P.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL‖

def CommutatorEstimate (P : VonNeumannAlgebra H) (C : ℝ) : Prop :=
  ∀ (Y : H →L[ℂ] H) (n : ℕ) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)),
    (∀ i j, X i j ∈ P) →
    ‖commutator (amplify Y n) (matrixOperator X)‖ ≤
      C * scalarCommutatorNorm P Y * ‖matrixOperator X‖

def UniformCommutatorEstimate (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : VonNeumannAlgebra K), CommutatorEstimate P C

def UniversalCommutatorTheorem : Prop := ∃ C : ℝ, 0 ≤ C ∧ UniformCommutatorEstimate.{u} C

def SimilarityTheorem : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (K : Type v) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (π : BoundedUnitalHom A K),
    SimilarToStar A K π

abbrev CommutantProjection (M : VonNeumannAlgebra H) :=
  {e : H →L[ℂ] H // e ∈ M.commutant ∧ star e = e ∧ e * e = e}

def offDiagonalSeminorm (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) : ℝ :=
  sSup (Set.range fun e : CommutantProjection M =>
    ‖(1 - (e : H →L[ℂ] H)) * T * (e : H →L[ℂ] H)‖)

def UniversalHyperreflexivity (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra K) (T : K →L[ℂ] K),
    Metric.infDist T (M : Set (K →L[ℂ] K)) ≤ 2 * C * offDiagonalSeminorm M T

end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def rowConstant : ℝ := 4 * Real.sqrt 2
def cyclicConstant : ℝ := (1 + 4 * rowConstant) ^ 2
def cornerConstant : ℝ := 6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant)
def factorConstant : ℝ := max (max (3 * cornerConstant + 2) (1 + 2 * rowConstant)) 2
def universalConstant : ℝ := 3 * factorConstant + 2

/-- One absolute constant controls every finite matrix commutator. -/
theorem universalCommutatorTheorem : UniversalCommutatorTheorem.{u} := by
  sorry

/-- Every von Neumann algebra has hyperreflexivity constant at most `2 * universalConstant`. -/
theorem universalHyperreflexivity : UniversalHyperreflexivity.{u} universalConstant := by
  sorry

/-- Every bounded unital representation is similar to a star representation. -/
theorem similarityTheorem : SimilarityTheorem.{u,v} := by
  sorry

end KadisonSimilarity

end

end OAI
