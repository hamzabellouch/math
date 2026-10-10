import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.MatrixRanks
import OAI.Analysis.JiangSu.MatrixAlgebras.FiniteCorners

namespace OAI

section

namespace Pureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma nonUnitalStarAlgHom_positive (φ : A →⋆ₙₐ[ℂ] B) (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
  obtain ⟨x, rfl⟩ := positive_square_factor a ha
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

lemma positivePower_nonUnital_map (φ : A →⋆ₙₐ[ℂ] B) (hφ : Continuous φ)
    (a : A) (ha : 0 ≤ a) (r : ℝ≥0) (hr : 0 < r) :
    positivePower (φ a) r = φ (positivePower a r) := by
  have hb := nonUnitalStarAlgHom_positive φ a ha
  have exponent_pos : (0 : ℝ) < r := hr
  simp only [positivePower, CFC.nnrpow_eq_pow,
    CFC.nnrpow_eq_cfcₙ_real a r ha, CFC.nnrpow_eq_cfcₙ_real (φ a) r hb]
  exact (φ.map_cfcₙ _ a (Real.continuous_rpow_const exponent_pos.le).continuousOn
    (Real.zero_rpow exponent_pos.ne') hφ ha.isSelfAdjoint hb.isSelfAdjoint).symm

variable {k l : ℕ}
lemma positivePower_corner (h : k ≤ l) (a : CStarMatrix (Fin k) (Fin k) A)
    (ha : 0 ≤ a) (r : ℝ≥0) (hr : 0 < r) :
    positivePower (corner h a) r = corner h (positivePower a r) :=
  positivePower_nonUnital_map (cornerHom h) (corner_isometry h).continuous a ha r hr

theorem matrixRank_corner [NeZero k] [NeZero l] (τ : TracialState A) (h : k ≤ l)
    (a : CStarMatrix (Fin k) (Fin k) A) (ha : 0 ≤ a) :
    matrixRank τ (corner h a) = matrixRank τ a := by
  apply tendsto_nhds_unique (matrixPower_trace_tendsto_rank τ (corner h a) (corner_nonneg h a ha))
  convert matrixPower_trace_tendsto_rank τ a ha using 1
  funext n
  rw [positivePower_corner h a ha _ (by positivity), matrixTrace_corner]

end Pureness
end

end OAI
