import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower
import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorTrace
import OAI.Analysis.KadisonSimilarity.Tracial.GNSVectorDensity
import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

/-! Coordinate maps for the actual increasing matrix stages. These maps
retain the concrete operators and their normalized traces. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H}

def concreteStageEquiv [Nontrivial N.toStarSubalgebra] (F : FiniteMatrixStage N) :
    Matrix (Fin F.size) (Fin F.size) ℂ ≃⋆ₐ[ℂ] F.units.concreteAlgebra := by
  letI : Nonempty (Fin F.size) := ⟨⟨0, F.positive⟩⟩
  exact StarAlgEquiv.ofInjective F.units.concreteHom
    (Subtype.val_injective.comp F.units.injective)

@[simp] theorem concreteStageEquiv_apply [Nontrivial N.toStarSubalgebra]
    (F : FiniteMatrixStage N) (a : Matrix (Fin F.size) (Fin F.size) ℂ) :
    ((concreteStageEquiv F a : F.units.concreteAlgebra) : H →L[ℂ] H) =
      F.units.concreteHom a := rfl

variable (F : ℕ → FiniteMatrixStage N)

def generatedStageEmbedding (n : ℕ) :
    Matrix (Fin (F n).size) (Fin (F n).size) ℂ →⋆ₐ[ℂ]
      (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra :=
  (F n).units.concreteHom.codRestrict (FiniteMatrixStage.generated F)
    (fun a => FiniteMatrixStage.stage_le_generated F n ⟨a, rfl⟩)

@[simp] theorem generatedStageEmbedding_apply (n : ℕ)
    (a : Matrix (Fin (F n).size) (Fin (F n).size) ℂ) :
    ((generatedStageEmbedding F n a :
      (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) : H →L[ℂ] H) =
      (F n).units.concreteHom a := rfl

def generatedMatrixTrace (υ : TracialRepresentation N) :
    (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra →ₚ[ℂ] ℂ :=
  vectorPositiveFunctional (FiniteMatrixStage.generatedVonNeumann F) υ.vector

def generatedMatrixVector (υ : TracialRepresentation N) :
    (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra →ₗ[ℂ] H :=
  baseVector (FiniteMatrixStage.generatedTrace F υ le_rfl)

@[simp] theorem generatedMatrixVector_apply (υ : TracialRepresentation N)
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    generatedMatrixVector F υ a = (a : H →L[ℂ] H) υ.vector := rfl

theorem generatedMatrixVector_inner (υ : TracialRepresentation N)
    (a b : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    inner ℂ (generatedMatrixVector F υ a) (generatedMatrixVector F υ b) =
      generatedMatrixTrace F υ (star a * b) :=
  baseVector_inner_trace (FiniteMatrixStage.generatedTrace F υ le_rfl) a b

theorem generatedMatrixTrace_dist (υ : TracialRepresentation N)
    (a b : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    dist (gnsTracialVector (generatedMatrixTrace F υ) a)
      (gnsTracialVector (generatedMatrixTrace F υ) b) =
      dist (generatedMatrixVector F υ a) (generatedMatrixVector F υ b) :=
  gns_dist_eq_of_trace_vectors (generatedMatrixTrace F υ) (generatedMatrixVector F υ)
    (generatedMatrixVector_inner F υ) a b

theorem generatedMatrixTrace_one (υ : TracialRepresentation N) :
    generatedMatrixTrace F υ 1 = 1 :=
  vectorPositiveFunctional_one _ υ.vector υ.norm_vector

theorem generatedMatrixTrace_tracial (υ : TracialRepresentation N)
    (a b : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    generatedMatrixTrace F υ (a * b) = generatedMatrixTrace F υ (b * a) :=
  (FiniteMatrixStage.generatedTrace F υ le_rfl).trace_mul_comm a b

theorem generatedMatrixTrace_faithful (υ : TracialRepresentation N)
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra)
    (ha : generatedMatrixTrace F υ (star a * a) = 0) : a = 0 := by
  have hz : generatedMatrixVector F υ a = 0 :=
    inner_self_eq_zero.mp ((generatedMatrixVector_inner F υ a a).trans ha)
  exact (FiniteMatrixStage.generatedTrace F υ le_rfl).separating a hz

theorem generatedMatrixTrace_normal (υ : TracialRepresentation N) :
    HasNormalGNS (generatedMatrixTrace F υ) :=
  hasNormalGNS_of_predual (concretePredualEquiv (FiniteMatrixStage.generatedVonNeumann F))
    (generatedMatrixTrace F υ) (vectorPositiveFunctional_normal _ υ.vector)
    (generatedMatrixTrace_tracial F υ)

variable [Nontrivial N.toStarSubalgebra]
  (hmono : Monotone (fun n => (F n).units.concreteAlgebra))

def generatedStageTransition (s t : ℕ) (h : s ≤ t) :
    Matrix (Fin (F s).size) (Fin (F s).size) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (F t).size) (Fin (F t).size) ℂ :=
  (concreteStageEquiv (F t)).symm.toStarAlgHom.comp
    ((StarSubalgebra.inclusion (hmono h)).comp (concreteStageEquiv (F s)).toStarAlgHom)

theorem generatedStageTransition_compatible (s t : ℕ) (h : s ≤ t)
    (a : Matrix (Fin (F s).size) (Fin (F s).size) ℂ) :
    generatedStageEmbedding F t (generatedStageTransition F hmono s t h a) =
      generatedStageEmbedding F s a := by
  apply Subtype.ext
  change (F t).units.concreteHom
      ((concreteStageEquiv (F t)).symm
        (StarSubalgebra.inclusion (hmono h) (concreteStageEquiv (F s) a))) =
    (F s).units.concreteHom a
  have he := (concreteStageEquiv (F t)).apply_symm_apply
    (StarSubalgebra.inclusion (hmono h) (concreteStageEquiv (F s) a))
  exact congrArg (fun b : (F t).units.concreteAlgebra => (b : H →L[ℂ] H)) he

omit [Nontrivial N.toStarSubalgebra] in
theorem generatedStageEmbedding_trace (υ : TracialRepresentation N) (n : ℕ)
    (a : Matrix (Fin (F n).size) (Fin (F n).size) ℂ) :
    generatedMatrixTrace F υ (generatedStageEmbedding F n a) =
        (Fintype.card (Fin (F n).size) : ℂ)⁻¹ * Matrix.trace a := by
  change υ.trace ((F n).units.hom a) = _
  exact (F n).units.trace_hom υ ⟨0, (F n).positive⟩ a

include hmono in
omit [Nontrivial N.toStarSubalgebra] in
theorem generatedStage_concrete_approximation (υ : TracialRepresentation N)
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n b, dist (generatedMatrixVector F υ (generatedStageEmbedding F n b))
      (generatedMatrixVector F υ a) < ε := by
  obtain ⟨n, b, hb⟩ := FiniteMatrixStage.exists_stage_strong_approximation F hmono a
    {υ.vector} ε hε
  obtain ⟨m, hm⟩ := b.property
  change (F n).units.concreteHom m = (b : H →L[ℂ] H) at hm
  refine ⟨n, m, ?_⟩
  rw [dist_eq_norm, generatedMatrixVector_apply,
    generatedMatrixVector_apply]
  change ‖(F n).units.concreteHom m υ.vector - (a : H →L[ℂ] H) υ.vector‖ < ε
  rw [hm, norm_sub_rev]
  exact hb υ.vector (Finset.mem_singleton_self _)

include hmono in
omit [Nontrivial N.toStarSubalgebra] in
theorem generatedStage_vector_approximation (υ : TracialRepresentation N)
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n b, dist (gnsTracialVector (generatedMatrixTrace F υ) (generatedStageEmbedding F n b))
      (gnsTracialVector (generatedMatrixTrace F υ) a) < ε := by
  obtain ⟨n, b, hb⟩ := generatedStage_concrete_approximation F hmono υ a ε hε
  exact ⟨n, b, (generatedMatrixTrace_dist F υ _ _).trans_lt hb⟩

include hmono in
omit [Nontrivial N.toStarSubalgebra] in
theorem generatedStage_vectors_dense (υ : TracialRepresentation N) :
    Dense (⋃ n, Set.range (fun a =>
      gnsTracialVector (generatedMatrixTrace F υ) (generatedStageEmbedding F n a))) :=
  gns_vectors_dense_of_approximation (generatedMatrixTrace F υ)
    (fun n a => generatedStageEmbedding F n a)
    (generatedStage_vector_approximation F hmono υ)

/-- The matrix presentation required by the commutator argument comes
from the actual increasing matrix subalgebras and their weak closure. -/
def concreteNestedTracialMatrices (υ : TracialRepresentation N) :
    NestedTracialMatrices (A := fun n => Fin (F n).size)
      (generatedMatrixTrace F υ).toLinearMap
      (gnsTracialVector (generatedMatrixTrace F υ)) where
  embedding := generatedStageEmbedding F
  trace_embedding := generatedStageEmbedding_trace F υ
  inclusion := generatedStageTransition F hmono
  compatible := generatedStageTransition_compatible F hmono
  dense := generatedStage_vectors_dense F hmono υ

end KadisonSimilarity

end

end OAI
