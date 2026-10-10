import OAI.Analysis.Laughlin.Asymptotics.LimitFourLocalSum
import OAI.Analysis.Laughlin.FourBody.LimitPositive
import OAI.Analysis.Laughlin.FourBody.TransferCoefficients
import OAI.Analysis.Laughlin.Operators.TruncatedFourCopy
import OAI.Analysis.Laughlin.Operators.TruncatedPairReturn

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

theorem source_fourBody_uniform_transfer (Q D : ℕ) (hQ : 24 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    -(fourBodyRho D Q * sourcePairWindow Q x) ≤
      occupationQuadratic Q (finiteFourMiddle Q D)
        (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D (by omega) x) := by
  let hDQ : D ≤ Q := by omega
  let v : LocalFourIndex D → Space Q := fun b =>
    localFourOperators Q D hDQ b (truncatedScaling 24 Q x)
  let ε := matrixMetricError 24 Q (finiteLocalFourMatrix Q D) (limitLocalFourMatrix D)
  let n : ℝ := Fintype.card (LocalFourIndex D)
  have hε : 0 ≤ ε := matrixMetricError_nonneg _ _ _ _
  have hn : 0 ≤ n := by positivity
  have hfinite : occupationQuadratic Q (finiteFourMiddle Q D)
      (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D hDQ x) =
      occupationQuadratic Q (finiteLocalFourMatrix Q D) (fun b => truncatedScalingInv 24 Q (v b)) := by
    simp_rw [physicalFourCopyEnd_truncated Q _ D hDQ hQ hD₂ x,map_sum,map_smul]
    exact occupationQuadratic_factor Q (finiteFourMiddle Q D) _ _
  rw [hfinite]
  have hbase := source_fourBody_limitpositive Q D (by omega) hD₁ hD₂ (truncatedScaling 24 Q x)
  change 0 ≤ occupationQuadratic Q (limitFourMiddle D)
    (fun i => limitFourCopyEnd Q (Certificate.copyLabel i) D (truncatedScaling 24 Q x)) at hbase
  have hends (i : Fin ((D+1)/2)) :
      limitFourCopyEnd Q (Certificate.copyLabel i) D (truncatedScaling 24 Q x) =
        ∑ b : LocalFourIndex D,
          (fourBodyLimitCoefficient (Certificate.copyLabel i) D D
            b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) • v b := by
    apply limitFourCopyEnd_local_sum Q _ D hDQ
    · unfold Certificate.copyLabel; have := i.isLt; omega
    · exact ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  simp_rw [hends] at hbase
  have hbase := hbase.trans_eq (occupationQuadratic_factor Q (limitFourMiddle D)
    (fun (i : Fin ((D+1)/2)) (b : LocalFourIndex D) =>
      fourBodyLimitCoefficient (Certificate.copyLabel i) D D b.val.1.val b.val.2.1.val b.val.2.2.val) v)
  change 0 ≤ occupationQuadratic Q (limitLocalFourMatrix D) v at hbase
  have herr := truncatedQuadratic_error 24 Q (finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) v ε hε (matrixMetricError_bound 24 Q hQ _ _)
  have hpair : (∑ b, occupationNormSq Q (v b)) ≤ n * sourcePairWindow Q x := by
    apply (localFourOperators_bound Q D hDQ hD₂ (truncatedScaling 24 Q x)).trans
    exact mul_le_mul_of_nonneg_left (truncated_pair_window_return Q hQ x) hn
  have hbound : |occupationQuadratic Q (finiteLocalFourMatrix Q D) (fun b => truncatedScalingInv 24 Q (v b)) -
      occupationQuadratic Q (limitLocalFourMatrix D) v| ≤ fourBodyRho D Q * sourcePairWindow Q x := by
    apply herr.trans
    calc
      _ ≤ ε*n*(n*sourcePairWindow Q x) := mul_le_mul_of_nonneg_left hpair (mul_nonneg hε hn)
      _ = _ := by change ε*n*(n*sourcePairWindow Q x)=(ε*n^2)*sourcePairWindow Q x; ring
  have hl := (abs_le.mp hbound).1
  linarith

noncomputable def uniformFourBodyRho (Q : ℕ) : ℝ := ∑ D ∈ Finset.range 24, fourBodyRho D Q

theorem uniformFourBodyRho_nonneg (Q : ℕ) : 0 ≤ uniformFourBodyRho Q :=
  Finset.sum_nonneg (fun degree _ => fourBodyRho_nonneg degree Q)

theorem uniformFourBodyRho_tendsto : Tendsto uniformFourBodyRho atTop (𝓝 0) := by
  have h := tendsto_finsetSum (s := Finset.range 24) (fun D hD => fourBodyRho_tendsto D)
  change Tendsto (fun Q => ∑ D ∈ Finset.range 24, fourBodyRho D Q) atTop (𝓝 0)
  simpa using h

theorem source_fourBody_uniform_transfer_all (Q D : ℕ) (hQ : 25 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    -(uniformFourBodyRho Q * sourcePairWindow Q x) ≤
      occupationQuadratic Q (finiteFourMiddle Q D)
        (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D (by omega) x) := by
  have hρ : fourBodyRho D Q ≤ uniformFourBodyRho Q :=
    Finset.single_le_sum (fun d hd => fourBodyRho_nonneg d Q) (Finset.mem_range.mpr (by omega))
  have he : 0 ≤ sourcePairWindow Q x := Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  exact (neg_le_neg (mul_le_mul_of_nonneg_right hρ he)).trans
    (source_fourBody_uniform_transfer Q D (by omega) hD₁ hD₂ x)

end Laughlin.Fock

end OAI
