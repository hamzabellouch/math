import OAI.Analysis.KadisonKastler.MatrixFactor
import OAI.Analysis.KadisonKastler.MatrixEmbedding
import OAI.Analysis.KadisonKastler.UnitaryLifts

namespace OAI

/-! # Actual unitary polar decompositions in finite matrix models

The scalar algebra is represented on the one-dimensional Hilbert space.
The proved matrix-von-Neumann bridge supplies concrete representations
of its finite matrix amplifications. Finite faithful trace and scalar
center then give the unitary polar decomposition.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A B ι : Type*} [CStarAlgebra A] [CStarAlgebra B] [Fintype ι] [DecidableEq ι]

/-- Entrywise transport along a star-algebra equivalence. -/
def coefficientMatrixEquiv (e : A ≃⋆ₐ[ℂ] B) : CStarMatrix ι ι A ≃⋆ₐ[ℂ] CStarMatrix ι ι B :=
  StarAlgEquiv.ofBijective (coefficientMatrixMap e.toStarAlgHom) (by
    constructor
    · intro x y h
      apply CStarMatrix.ext
      intro i j
      apply e.injective
      exact congrArg (fun z : CStarMatrix ι ι B => z i j) h
    · intro y
      refine ⟨CStarMatrix.ofMatrix (fun i j => e.symm (y i j)), ?_⟩
      apply CStarMatrix.ext
      intro i j
      exact e.apply_symm_apply (y i j))

@[simp]
theorem coefficientMatrixEquiv_apply (e : A ≃⋆ₐ[ℂ] B) (x : CStarMatrix ι ι A) (i j : ι) :
    coefficientMatrixEquiv e x i j = e (x i j) := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Amplify a concrete representation by a finite matrix algebra. -/
def matrixRepresentationEquiv (e : A ≃⋆ₐ[ℂ] Algebra M) :
    CStarMatrix ι ι A ≃⋆ₐ[ℂ] Algebra (matrixVonNeumann (ι := ι) M) :=
  (coefficientMatrixEquiv e).trans (matrixAlgebraEquiv M)

/-- Scalar center transports along any star equivalence. -/
theorem scalar_center_equiv (e : A ≃⋆ₐ[ℂ] B)
    (hA : ∀ a : A, (∀ b : A, b * a = a * b) → ∃ z : ℂ, a = z • (1 : A))
    (b : B) (hb : ∀ c : B, c * b = b * c) : ∃ z : ℂ, b = z • (1 : B) := by
  have ha : ∀ a : A, a * e.symm b = e.symm b * a := by
    intro a
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm (hb (e a))
  obtain ⟨z, hz⟩ := hA (e.symm b) ha
  refine ⟨z, ?_⟩
  calc
    b = e (e.symm b) := (e.apply_symm_apply b).symm
    _ = e (z • 1) := congrArg e hz
    _ = z • 1 := equiv_smul_one e z

local instance finitePolarSourceOrder : PartialOrder A := CStarAlgebra.spectralOrder _
local instance finitePolarSourceStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance finitePolarRepresentedOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance finitePolarRepresentedPreorder : Preorder (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance finitePolarRepresentedLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance finitePolarRepresentedStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The finite-factor polar theorem needs a concrete von Neumann
representation, scalar center, and finite faithful trace; no diffuseness. -/
theorem unitary_polar_of_representation (e : A ≃⋆ₐ[ℂ] Algebra M)
    (τ : FaithfulTracialState A)
    (hA : ∀ a : A, (∀ b : A, b * a = a * b) → ∃ z : ℂ, a = z • (1 : A))
    (x : A) : ∃ u : unitary A, (u : A) * CFC.abs x = x := by
  have hc := scalar_center_equiv e hA
  have hf : ∀ v : Algebra M, star v * v = 1 → v * star v = 1 :=
    fun v hv => isometry_coisometry_of_faithfulTrace (τ.comapStarAlgEquiv e.symm) v hv
  obtain ⟨u, hu⟩ := Generator.Tracial.exists_unitary_polar_decomposition hc hf (e x)
  change (u : Algebra M) * CFC.abs (e x) = e x at hu
  let φ := e.symm.toStarAlgHom
  let v : unitary A := Unitary.map (StarMonoidHom.ofClass φ) u
  refine ⟨v, ?_⟩
  have hh := congrArg φ hu
  rw [map_mul, starAlgHom_map_abs] at hh
  change e.symm (u : Algebra M) * CFC.abs x = x
  change e.symm (u : Algebra M) * CFC.abs (e.symm (e x)) = e.symm (e x) at hh
  simpa only [e.symm_apply_apply] using hh

/-- The full operator algebra on the one-dimensional Hilbert space. -/
def scalarVonNeumann : VonNeumannAlgebra ℂ where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (∅ : Set (ℂ →L[ℂ] ℂ))
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

theorem scalar_ofId_apply (z w : ℂ) :
    ((StarAlgHom.ofId ℂ (Algebra scalarVonNeumann)) z).val w = z * w := by
  change (z • (1 : ℂ →L[ℂ] ℂ)) w = z * w
  rfl

/-- Multiplication on C identifies it with its full bounded-operator algebra. -/
def scalarRepresentation : ℂ ≃⋆ₐ[ℂ] Algebra scalarVonNeumann :=
  StarAlgEquiv.ofBijective (StarAlgHom.ofId ℂ (Algebra scalarVonNeumann)) (by
    constructor
    · intro z w h
      have he := congrArg (fun T : Algebra scalarVonNeumann => T.val 1) h
      simpa only [scalar_ofId_apply, mul_one] using he
    · intro T
      refine ⟨T.val 1, ?_⟩
      apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro z
      rw [scalar_ofId_apply]
      have hz := T.val.map_smul z (1 : ℂ)
      simpa only [smul_eq_mul, mul_one, mul_comm] using hz.symm)

local instance finitePolarComplexOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance finitePolarComplexStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

/-- The concrete Hilbert-space representation of each nested finite matrix model. -/
def finiteMatrixRepresentation (n j : ℕ) : FiniteMatrixModel n j ≃⋆ₐ[ℂ]
    Algebra (matrixVonNeumann (ι := Fin n)
      (matrixVonNeumann (ι := Fin (j + 1)) scalarVonNeumann)) :=
  matrixRepresentationEquiv (matrixRepresentationEquiv scalarRepresentation)

theorem finiteMatrixModel_scalar_center (n j : ℕ) (x : FiniteMatrixModel n j)
    (hx : ∀ y : FiniteMatrixModel n j, y * x = x * y) :
    ∃ z : ℂ, x = z • (1 : FiniteMatrixModel n j) := by
  apply matrix_scalar_center ?_ x hx
  intro a ha
  apply matrix_scalar_center ?_ a ha
  intro z hz
  exact ⟨z, by simp⟩

local instance finiteModelPolarOrder (n j : ℕ) : PartialOrder (FiniteMatrixModel n j) :=
  CStarAlgebra.spectralOrder _
local instance finiteModelPolarStarOrder (n j : ℕ) : StarOrderedRing (FiniteMatrixModel n j) :=
  CStarAlgebra.spectralOrderedRing _

local instance finiteModelRealFunctionalCalculus (n j : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (FiniteMatrixModel n j) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance finiteModelNonnegSpectrum (n j : ℕ) :
    NonnegSpectrumClass ℝ (FiniteMatrixModel n j) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- Every element of the actual finite-matrix coordinate has a unitary
polar factor; the statement supplies the hypothesis used for varying lifts. -/
theorem finiteMatrixModel_unitary_polar (n j : ℕ) [NeZero n] (x : FiniteMatrixModel n j) :
    ∃ u : unitary (FiniteMatrixModel n j), (u : FiniteMatrixModel n j) * CFC.abs x = x :=
  unitary_polar_of_representation (finiteMatrixRepresentation n j)
    (finiteMatrixModelTrace n j) (finiteMatrixModel_scalar_center n j) x

end

end KadisonKastler

end OAI
