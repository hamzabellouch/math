import OAI.Analysis.KadisonKastler.TracialPartitionRemainder
import OAI.Analysis.KadisonKastler.FiniteProjectionAveraging

namespace OAI

/-! # Finite matrix averaging of rounded spectral sums -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

/-- A common matrix-algebra remainder controls the norm error of a whole
spectral sum after one finite average. -/
theorem exists_scalar_average_of_rounded_partition (τ : TracialRepresentation M)
    (Q : CornerPartition (identityProjection M)) (q : Fin Q.size → AlgebraProjection M)
    (hq : ∀ i, q i ≤ Q.piece i) {n : ℕ} [Nonempty (Fin n)]
    (E : MatrixUnitSystem (Fin n) (Algebra M))
    (hmem : ∀ i, (q i).val ∈ E.algebra)
    (c : Fin Q.size → ℂ) (η : ℝ)
    (hη : (τ.trace (partitionRemainder Q q hq).val).re ≤ η) :
    ∃ (A : FiniteInnerAverage M) (z : ℂ),
      ‖A.apply (∑ i, c i • (Q.piece i).val.val) - z • (1 : H →L[ℂ] H)‖ ≤
        (∑ i, ‖c i‖) * η := by
  let F := E.map M.toStarSubalgebra.subtype
  have hF : F.algebra ≤ M.toStarSubalgebra :=
    (F.algebra_le_iff _).mpr (fun i j => (E.entry i j).property)
  let A := matrixInnerAverage F hF
  let y : Algebra M := ∑ i, c i • (q i).val
  let r := partitionRemainder Q q hq
  let L : Algebra M →ₗ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype.toAlgHom.toLinearMap
  have map_mem (x : Algebra M) (hx : x ∈ E.algebra) : x.val ∈ F.algebra := by
    obtain ⟨a, ha⟩ := E.mem_algebra x |>.mp hx
    rw [← ha]
    change L (∑ i, ∑ j, a i j • E.entry i j) ∈ F.algebra
    rw [map_sum]
    apply F.algebra.sum_mem
    intro i _
    rw [map_sum]
    apply F.algebra.sum_mem
    intro j _
    rw [L.map_smul]
    exact F.algebra.smul_mem (F.entry_mem i j) _
  have hy : y ∈ E.algebra := E.algebra.sum_mem (fun i _ => E.algebra.smul_mem (hmem i) _)
  have hr : r.val ∈ E.algebra := partitionRemainder_mem Q q hq E.algebra hmem
  have hAy : A.apply y.val = τ.trace y • (1 : H →L[ℂ] H) :=
    tracial_matrixUnitAverage_eq_trace τ F hF y (map_mem y hy)
  have hAr : A.apply r.val.val = algebraMap ℝ (H →L[ℂ] H) (τ.trace r.val).re := by
    change matrixUnitAverage F r.val.val = _
    rw [tracial_matrixUnitAverage_eq_trace τ F hF r.val (map_mem r.val hr),
      projection_trace_real τ r, Algebra.algebraMap_eq_smul_one]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (τ.trace r.val).re
      (1 : H →L[ℂ] H)).symm
  have hb (i : Fin Q.size) :
      ‖A.apply (partitionResidual Q q hq i).val.val‖ ≤ η := by
    have hp := (partitionResidual Q q hq i).property.map M.toStarSubalgebra.subtype
    exact (A.norm_apply_le_of_positive_interval _ r.val.val (τ.trace r.val).re
      (by rw [projection_trace_sq τ r.val r.property]; positivity) hp.nonneg
      (ambient_projection_le (partitionResidual_le_remainder Q q hq i)) hAr).trans hη
  refine ⟨A, τ.trace y, ?_⟩
  rw [← hAy, ← A.apply_sub]
  have he : (∑ i, c i • (Q.piece i).val.val) - y.val =
      ∑ i, c i • (partitionResidual Q q hq i).val.val := by
    change (∑ i, c i • (Q.piece i).val.val) -
      M.toStarSubalgebra.subtype (∑ i, c i • (q i).val) = _
    simp only [map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
    rfl
  rw [he]
  change ‖A.linear (∑ i, c i • (partitionResidual Q q hq i).val.val)‖ ≤ _
  rw [map_sum]
  calc
    ‖∑ i, A.linear (c i • (partitionResidual Q q hq i).val.val)‖ ≤
        ∑ i, ‖A.linear (c i • (partitionResidual Q q hq i).val.val)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ * η := Finset.sum_le_sum (fun i _ => by
      rw [map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
    _ = (∑ i, ‖c i‖) * η := (Finset.sum_mul ..).symm

end

end KadisonKastler

end OAI
