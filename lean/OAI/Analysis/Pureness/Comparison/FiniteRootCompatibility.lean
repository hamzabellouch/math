import OAI.Analysis.Pureness.Comparison.TracialExtendedTrace

namespace OAI
noncomputable section
open scoped CStarAlgebra ComplexOrder ENNReal NNReal Topology
open Filter MeasureTheory
namespace CuntzComparison
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma shared_positive_root {n : ℕ} (a : Positive (FinMatrix A n)) (k : ℕ) :
    (Positive.power (Positive.rootExponent k) a).1 = CFC.rpow a.1 (1 / ((k : ℝ)+1)) := by
  change CFC.nnrpow a.1 (Positive.rootExponent k) = _
  rw [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_rpow (Positive.rootExponent_pos k)]
  congr 1

theorem TracialState.extended_matrixRank (τ : TracialState A) {n : ℕ} [NeZero n]
    (a : Positive (FinMatrix A n)) :
    (τ.extendedTrace.matrixTrace (Fin n)).rank a = τ.matrixSupportMass a.1 a.2 := by
  have hroot := (τ.extendedTrace.matrixTrace (Fin n)).tendsto_roots_rank_all a
  have hspec := ENNReal.continuous_ofReal.tendsto ((τ.matrixSupportMass a.1 a.2).toReal) |>.comp
    (τ.matrix_root_trace_tendsto a.2)
  have hfinite : τ.matrixSupportMass a.1 a.2 ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · exact measure_ne_top _ _
  rw [ENNReal.ofReal_toReal hfinite] at hspec
  apply tendsto_nhds_unique hroot
  have he : (fun k => τ.extendedTrace.matrixTrace (Fin n) (Positive.power (Positive.rootExponent k) a)) =
      (fun k : ℕ => ENNReal.ofReal (τ.matrixTraceLinear (CFC.rpow a.1 (1 / ((k : ℝ)+1)))).re) := by
    funext k
    rw [τ.extended_matrixTrace, shared_positive_root]
  rw [he]
  exact hspec
end CuntzComparison

end

end OAI
