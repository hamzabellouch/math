import OAI.Analysis.KadisonSimilarity.FreeProduct.CompactHaarIntegrability
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

namespace OAI

/-! The finite-factor averaging stage uses actual normalized Haar measures
on the finite matrix-unitary groups. Their continuity and weak integrability
are proved here; the resulting operator is within the original scalar
commutator bound and has scalar commutator bound at most three times it. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory TopologicalSpace
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

section SingleStage

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Restriction of a matrix representation to its unitary group. -/
def matrixUnitaryAction (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Matrix.unitaryGroup α ℂ →* (H →L[ℂ] H) :=
  R.toMonoidHom.comp (unitary (Matrix α α ℂ)).subtype

theorem matrixUnitaryAction_norm_le (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (u : Matrix.unitaryGroup α ℂ) : ‖matrixUnitaryAction R u‖ ≤ 1 := by
  let w := Unitary.map (StarMonoidHom.ofClass R) u
  change ‖(w : H →L[ℂ] H)‖ ≤ 1
  exact (Unitary.linearIsometryEquiv w).toLinearIsometry.norm_toContinuousLinearMap_le

theorem matrixUnitaryAction_adjoint (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (u : Matrix.unitaryGroup α ℂ) :
    (matrixUnitaryAction R u).adjoint = matrixUnitaryAction R u⁻¹ := by
  change (R (u : Matrix α α ℂ)).adjoint = R (↑u⁻¹ : Matrix α α ℂ)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  congr 1

/-- Finite-dimensional continuity proves strong continuity of the action. -/
theorem matrixUnitaryAction_continuous (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    Continuous (fun u : Matrix.unitaryGroup α ℂ => matrixUnitaryAction R u x) := by
  have hR : Continuous R := R.toAlgHom.toLinearMap.continuous_of_finiteDimensional
  exact (hR.comp continuous_subtype_val).clm_apply continuous_const

/-- Commutation with matrix unitaries implies commutation with every matrix,
by the four-unitary spanning theorem in the actual C-star matrix algebra. -/
theorem commutes_matrix_of_unitaries [Nonempty α]
    (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : H →L[ℂ] H) (hS : ∀ u, commutator S (matrixUnitaryAction R u) = 0)
    (a : Matrix α α ℂ) : commutator S (R a) = 0 := by
  let φ : CStarMatrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    R.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom
  obtain ⟨u, c, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary (CStarMatrix.ofMatrix a)
  have hu (i : Fin 4) : commutator S (φ (u i : CStarMatrix α α ℂ)) = 0 := by
    let v : Matrix.unitaryGroup α ℂ :=
      Unitary.map (StarMonoidHom.ofClass CStarMatrix.ofMatrixStarAlgEquiv.symm) (u i)
    exact hS v
  have he : R a = ∑ i, c i • φ (u i : CStarMatrix α α ℂ) := by
    change φ (CStarMatrix.ofMatrix a) = _
    rw [ha, map_sum]
    simp only [map_smul]
  rw [he]
  unfold commutator
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
  change c i • commutator S (φ (u i : CStarMatrix α α ℂ)) = 0
  rw [hu, smul_zero]

end SingleStage

local instance finiteMatrixUnitaryCompactSpace (n : ℕ) :
    CompactSpace (Matrix.unitaryGroup (I n) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : I n =>
      Set.pi Set.univ fun _ : I n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  apply hK.of_isClosed_subset (isClosed_unitary (R := Matrix (I n) (I n) ℂ))
  intro x hx i _ j _
  change dist (x i j) 0 ≤ 1
  rw [dist_zero_right]
  exact entry_norm_bound_of_unitary hx i j

local instance finiteMatrixUnitaryMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (I n) ℂ) := borel _
local instance finiteMatrixUnitaryBorelSpace (n : ℕ) :
    BorelSpace (Matrix.unitaryGroup (I n) ℂ) := ⟨rfl⟩

/-- Normalized Haar measure on each actual finite matrix-unitary group. -/
def finiteMatrixHaarProbability (n : ℕ) : Measure (Matrix.unitaryGroup (I n) ℂ) :=
  Measure.haarMeasure ⊤

instance finiteMatrixHaarProbability_probability (n : ℕ) :
    IsProbabilityMeasure (finiteMatrixHaarProbability (I := I) n) := by
  apply IsProbabilityMeasure.mk
  exact Measure.haarMeasure_self
    (K₀ := (⊤ : PositiveCompacts (Matrix.unitaryGroup (I n) ℂ)))

instance finiteMatrixHaarProbability_leftInvariant (n : ℕ) :
    (finiteMatrixHaarProbability (I := I) n).IsMulLeftInvariant :=
  inferInstanceAs (Measure.haarMeasure
    (⊤ : PositiveCompacts (Matrix.unitaryGroup (I n) ℂ))).IsMulLeftInvariant

/-- Actual Haar averaging over increasing matrix stages produces the
finite-factor perturbation with the manuscript's factor-three estimate. -/
theorem exists_finite_matrix_symmetrization
    [∀ n, Nonempty (I n)]
    (M : VonNeumannAlgebra H)
    (R : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hmem : ∀ n a, R n a ∈ M)
    (ι : ∀ n m, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (hcompat : ∀ n m h a, R m (ι n m h a) = R n a)
    (Y : H →L[ℂ] H) :
    ∃ Y₀ : H →L[ℂ] H, ‖Y₀‖ ≤ ‖Y‖ ∧
      ‖Y₀ - Y‖ ≤ scalarCommutatorNorm M Y ∧
      scalarCommutatorNorm M Y₀ ≤ 3 * scalarCommutatorNorm M Y ∧
      ∀ n a, commutator Y₀ (R n a) = 0 := by
  let U := fun n => matrixUnitaryAction (R n)
  let emb := fun n m h =>
    Unitary.map (StarMonoidHom.ofClass (ι n m h))
  have hc n m h u : U m (emb n m h u) = U n u := hcompat n m h u
  have hI n : WeaklyIntegrable (finiteMatrixHaarProbability (I := I) n)
      (unitaryConjugate (U n) Y) :=
    weaklyIntegrable_unitaryConjugate _ _ (matrixUnitaryAction_adjoint (R n))
      (matrixUnitaryAction_continuous (R n)) Y
  obtain ⟨Y₀, hnorm, hclose, hscalar, hinv⟩ := exists_scalar_symmetrization
    (finiteMatrixHaarProbability (I := I)) M U
    (fun n => matrixUnitaryAction_norm_le (R n)) (fun n u => hmem n u)
    (fun n m h u => emb n m h u) hc Y hI
  exact ⟨Y₀, hnorm, hclose, hscalar, fun n => commutes_matrix_of_unitaries (R n) Y₀ (hinv n)⟩

/-- Double-commutant generation extends the finite-stage conclusion to the
whole generated subfactor. No extra invariant operator is assumed. -/
theorem exists_generated_factor_symmetrization
    [∀ n, Nonempty (I n)]
    (M N : VonNeumannAlgebra H)
    (R : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hmem : ∀ n a, R n a ∈ M)
    (ι : ∀ n m, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (hcompat : ∀ n m h a, R m (ι n m h a) = R n a)
    (hgenerate : (N : Set (H →L[ℂ] H)) = Set.centralizer
      (Set.centralizer {x | ∃ n a, R n a = x}))
    (Y : H →L[ℂ] H) :
    ∃ Y₀ : H →L[ℂ] H, ‖Y₀‖ ≤ ‖Y‖ ∧
      ‖Y₀ - Y‖ ≤ scalarCommutatorNorm M Y ∧
      scalarCommutatorNorm M Y₀ ≤ 3 * scalarCommutatorNorm M Y ∧
      ∀ a : H →L[ℂ] H, a ∈ N → commutator Y₀ a = 0 := by
  obtain ⟨Y₀, hnorm, hclose, hscalar, hinv⟩ :=
    exists_finite_matrix_symmetrization M R hmem ι hcompat Y
  refine ⟨Y₀, hnorm, hclose, hscalar, ?_⟩
  have hc : Y₀ ∈ Set.centralizer {x | ∃ n a, R n a = x} := by
    rintro x ⟨n, a, rfl⟩
    exact (sub_eq_zero.mp (hinv n a)).symm
  intro a ha
  change a ∈ (N : Set (H →L[ℂ] H)) at ha
  rw [hgenerate] at ha
  exact sub_eq_zero.mpr (ha Y₀ hc)

end KadisonSimilarity

end

end OAI
