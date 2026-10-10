import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights
import OAI.Analysis.JiangSu.TraceCone.CompactOperators

namespace OAI


noncomputable section
open scoped Topology InnerProductSpace
open Filter

namespace TraceCone

abbrev StandardOperators := StandardHilbert →L[ℂ] StandardHilbert

local instance : ContinuousStar StandardOperators where
  continuous_star :=
    (ContinuousLinearMap.adjoint : StandardOperators ≃ₗᵢ⋆[ℂ] StandardOperators).continuous

def matrixUnitGenerators : Set StandardOperators :=
  {T | ∃ i j : ℕ, T = (compactMatrixUnit i j : StandardOperators)}

def matrixUnitAlgebra : NonUnitalStarSubalgebra ℂ StandardOperators :=
  NonUnitalStarAlgebra.adjoin ℂ matrixUnitGenerators

lemma single_eq_smul_standardVector (i : ℕ) (z : ℂ) :
    lp.single 2 i z = z • standardVector i := by
  ext j
  simp [standardVector, Pi.single_apply]

lemma rankOne_single_single (i j : ℕ) (a b : ℂ) :
    InnerProductSpace.rankOne ℂ (lp.single 2 i a) (lp.single 2 j b) =
      (a * star b) • (compactMatrixUnit i j : StandardOperators) := by
  rw [single_eq_smul_standardVector, single_eq_smul_standardVector]
  ext z
  simp [compactMatrixUnit, InnerProductSpace.rankOne_apply, smul_smul, mul_comm]

def standardPartialVector (s : Finset ℕ) (x : StandardHilbert) : StandardHilbert :=
  ∑ i ∈ s, lp.single 2 i (x i)

lemma standardPartialVector_tendsto (x : StandardHilbert) :
    Tendsto (fun s => standardPartialVector s x) atTop (𝓝 x) :=
  lp.hasSum_single ENNReal.ofNat_ne_top x

lemma single_rankOne_mem_matrixUnitClosure (i j : ℕ) (a b : ℂ) :
    InnerProductSpace.rankOne ℂ (lp.single 2 i a) (lp.single 2 j b) ∈ matrixUnitAlgebra.topologicalClosure := by
  rw [rankOne_single_single]
  apply matrixUnitAlgebra.topologicalClosure.smul_mem
  apply NonUnitalStarSubalgebra.le_topologicalClosure
  exact NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨i,j,rfl⟩

lemma rankOne_right_partial_tendsto (x y : StandardHilbert) :
    Tendsto (fun s => InnerProductSpace.rankOne ℂ x (standardPartialVector s y))
      atTop (𝓝 (InnerProductSpace.rankOne ℂ x y)) :=
  ((InnerProductSpace.rankOne ℂ x : StandardHilbert →L⋆[ℂ] StandardOperators).continuous.tendsto y).comp
    (standardPartialVector_tendsto y)

lemma leftSingle_rankOne_mem_matrixUnitClosure (i : ℕ) (a : ℂ) (y : StandardHilbert) :
    InnerProductSpace.rankOne ℂ (lp.single 2 i a) y ∈ matrixUnitAlgebra.topologicalClosure := by
  have ht := rankOne_right_partial_tendsto (lp.single 2 i a) y
  apply (NonUnitalStarSubalgebra.isClosed_topologicalClosure matrixUnitAlgebra).mem_of_tendsto ht
  apply Eventually.of_forall
  intro s
  simp only [standardPartialVector, map_sum]
  exact matrixUnitAlgebra.topologicalClosure.sum_mem (fun j _ => single_rankOne_mem_matrixUnitClosure i j a (y j))

theorem rankOne_mem_matrixUnitClosure (x y : StandardHilbert) :
    InnerProductSpace.rankOne ℂ x y ∈ matrixUnitAlgebra.topologicalClosure := by
  have ht : Tendsto (fun s => ((InnerProductSpace.rankOne ℂ).flip y) (standardPartialVector s x))
      atTop (𝓝 (InnerProductSpace.rankOne ℂ x y)) :=
    ((((InnerProductSpace.rankOne ℂ : StandardHilbert →L[ℂ] StandardHilbert →L⋆[ℂ] StandardOperators).flip y)).continuous.tendsto x).comp
      (standardPartialVector_tendsto x)
  apply (NonUnitalStarSubalgebra.isClosed_topologicalClosure matrixUnitAlgebra).mem_of_tendsto ht
  apply Eventually.of_forall
  intro s
  simp only [standardPartialVector, map_sum]
  exact matrixUnitAlgebra.topologicalClosure.sum_mem (fun i _ => leftSingle_rankOne_mem_matrixUnitClosure i (x i) y)

theorem matrixUnitClosure_eq_compactOperatorAlgebra :
    matrixUnitAlgebra.topologicalClosure = compactOperatorAlgebra StandardHilbert := by
  apply le_antisymm
  · apply NonUnitalStarSubalgebra.topologicalClosure_minimal
    · apply NonUnitalStarAlgebra.adjoin_le
      rintro T ⟨i,j,rfl⟩
      exact (compactMatrixUnit i j).2
    · exact compactOperatorAlgebra_closed _
  · apply NonUnitalStarSubalgebra.topologicalClosure_minimal
    · apply NonUnitalStarAlgebra.adjoin_le
      rintro T ⟨x,y,rfl⟩
      exact rankOne_mem_matrixUnitClosure x y
    · exact NonUnitalStarSubalgebra.isClosed_topologicalClosure _
end TraceCone
end

end OAI
