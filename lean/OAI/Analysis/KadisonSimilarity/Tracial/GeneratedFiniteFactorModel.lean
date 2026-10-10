import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteFiniteFactorModel
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixStageGrowth

namespace OAI

/-! The constructed matrix subfactor in a normal trace representation
supplies the finite-factor model in the original representation. Only the
prescribed ultrapower free position remains a local input. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {P : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (υ : TracialRepresentation N)
  (e : P.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
  (he : ∀ a, υ.trace (e a) = τ a) (F : ℕ → FiniteMatrixStage N)

def generatedOriginalInclusion :
    (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra →⋆ₐ[ℂ] P.toStarSubalgebra :=
  e.symm.toStarAlgHom.comp (StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F))

include he in
theorem generatedOriginalInclusion_trace
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    τ (generatedOriginalInclusion e F a) = generatedMatrixTrace F υ a := by
  change τ (e.symm (StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F) a)) =
    υ.trace (StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F) a)
  have h := he (e.symm (StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F) a))
  simpa only [e.apply_symm_apply] using h.symm

variable [Nontrivial N.toStarSubalgebra]
  (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0) (hnormal : HasNormalGNS τ)
  (hmono : Monotone (fun n => (F n).units.concreteAlgebra))
  (hdiff : ∀ p : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra,
    IsStarProjection p → p ≠ 0 → ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
      p * q = q ∧ q * p = q)
  (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
  (free_position : FiniteFactorFreeCornerInputs (generatedMatrixTrace F υ) τ
    (generatedMatrixTrace_one F υ) h1 ω (generatedMatrixTrace_tracial F υ) htr
    (generatedOriginalInclusion e F) (generatedOriginalInclusion_trace τ υ e he F) hω)

local instance generatedStageNonempty (n : ℕ) : Nonempty (Fin (F n).size) :=
  ⟨⟨0, (F n).positive⟩⟩

/-- No matrix presentation, matrix-size divergence, or source-trace
properties are assumed separately from the constructed diffuse subfactor. -/
def generatedFiniteFactorModel : FiniteFactorModel P where
  R := (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra
  traceR := generatedMatrixTrace F υ
  traceP := τ
  oneR := generatedMatrixTrace_one F υ
  oneP := h1
  tracialR := generatedMatrixTrace_tracial F υ
  tracialP := htr
  faithfulR := generatedMatrixTrace_faithful F υ
  faithfulP := hf
  normalR := generatedMatrixTrace_normal F υ
  normalP := hnormal
  inclusion := generatedOriginalInclusion e F
  trace_inclusion := generatedOriginalInclusion_trace τ υ e he F
  size := fun n => (F n).size
  stageNonempty := generatedStageNonempty F
  matrices := concreteNestedTracialMatrices F hmono υ
  size_tendsto := matrix_stage_sizes_tendsto F hmono hdiff
  omega := ω
  omega_cofinite := hω
  localInputs := free_position

end KadisonSimilarity

end

end OAI
