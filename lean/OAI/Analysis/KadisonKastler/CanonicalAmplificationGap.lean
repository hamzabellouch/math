import OAI.Analysis.KadisonKastler.CanonicalAmplification
import OAI.Analysis.KadisonKastler.AmplificationGap

namespace OAI

/-! # The canonical amplification gap from common matrix units

Actual countable matrix units transport under a Hilbert-space isometry.
Thus the common-matrix-unit gap estimate applies to the canonical Hilbert
sum of the original representation, retaining its original tolerance.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {D : Submodule ℂ H} [CompleteSpace D]

namespace FullMatrixCorner

variable (F : FullMatrixCorner D)

omit [CompleteSpace H] [CompleteSpace K] in
instance spatialTransportSubspaceComplete (e : H ≃ₗᵢ[ℂ] K) :
    CompleteSpace (D.map e.toLinearEquiv.toLinearMap) :=
  e.toLinearIsometry.completeSpace_map D

/-- Transport of all the matrix units, including the strong sum condition. -/
def spatialTransport (e : H ≃ₗᵢ[ℂ] K) :
    FullMatrixCorner (D.map e.toLinearEquiv.toLinearMap) where
  entry i j := e.conjStarAlgEquiv (F.entry i j)
  star_entry i j := by
    calc
      star (e.conjStarAlgEquiv (F.entry i j)) =
          e.conjStarAlgEquiv (star (F.entry i j)) :=
        (StarHomClass.map_star e.conjStarAlgEquiv (F.entry i j)).symm
      _ = e.conjStarAlgEquiv (F.entry j i) :=
        congrArg e.conjStarAlgEquiv (F.star_entry i j)
  mul_entry i j k l := by
    rw [← map_mul, F.mul_entry]
    split_ifs <;> simp only [map_zero]
  zero_zero := by
    rw [F.zero_zero]
    apply ContinuousLinearMap.ext
    intro x
    exact (Submodule.starProjection_map_apply e D x).symm
  total x := by
    have h := e.toContinuousLinearEquiv.toContinuousLinearMap.hasSum (F.total (e.symm x))
    change HasSum (fun i => e (F.entry i i (e.symm x))) (e (e.symm x)) at h
    rw [e.apply_symm_apply] at h
    exact h

@[simp] theorem spatialTransport_entry (e : H ≃ₗᵢ[ℂ] K) (i j : ℕ) :
    (F.spatialTransport e).entry i j = e.conjStarAlgEquiv (F.entry i j) := rfl

theorem spatialTransport_entry_mem (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (i j : ℕ) :
    (F.spatialTransport e).entry i j ∈ spatialTransportAlgebra e M :=
  ⟨F.entry i j, hM i j, rfl⟩

end FullMatrixCorner

/-- Countably many common original matrix units control the actual
canonical countable amplification with the same gap. -/
theorem kkDistance_canonicalAmplifiedAlgebra_le_of_common_matrix_units
    (M N : VonNeumannAlgebra H) (F : FullMatrixCorner D)
    (hM : ∀ i j, F.entry i j ∈ M) (hN : ∀ i j, F.entry i j ∈ N) :
    kkDistance (canonicalAmplifiedAlgebra H M) (canonicalAmplifiedAlgebra H N) ≤
      kkDistance M N := by
  have h := (canonicalMatrixCorner H).kkDistance_amplifiedAlgebra_le_of_common_matrix_units
    (canonicalCornerAlgebra H M) (canonicalCornerAlgebra H N)
    (D.map (canonicalInitialEquiv H).toLinearEquiv.toLinearMap)
    (F.spatialTransport (canonicalInitialEquiv H))
    (F.spatialTransport_entry_mem (canonicalInitialEquiv H) M hM)
    (F.spatialTransport_entry_mem (canonicalInitialEquiv H) N hN)
  exact h.trans_eq (kkDistance_canonicalCornerAlgebra H M N)

end

end KadisonKastler

end OAI
