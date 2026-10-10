import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternGroundFinite
import OAI.Probability.InvariantIsing.Core.CubeOperatorNorm
import OAI.Probability.InvariantIsing.Core.FiniteSquareExtrema
import OAI.Probability.InvariantIsing.Core.FiniteOperatorDuality

namespace OAI

/-! Exact finite Gaussian norm and minimum identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators
namespace InvariantIsing

def gaussianPatternColumn {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (i : Fin N) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => z (i,j))

lemma gaussianPatternSum_eq_sum {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) (σ : Spin N) :
    gaussianPatternSum z σ=∑ i, spinValue (σ i) • gaussianPatternColumn z i := by
  ext j
  simp [gaussianPatternSum,gaussianPatternArray,gaussianPatternColumn,Matrix.mulVec,
    dotProduct,mul_comm]

def gaussianPatternOperator {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    ((gaussianPatternArray z)ᵀ.mulVecLin.toContinuousLinearMap)

def gaussianPatternTransposeOperator {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] PiLp 1 (fun _ : Fin N => ℝ) :=
  ((PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin N => ℝ)).symm.toContinuousLinearMap.comp
    ((gaussianPatternArray z).mulVecLin.toContinuousLinearMap)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).toContinuousLinearMap

lemma gaussianPattern_transpose_norm {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ‖gaussianPatternTransposeOperator z‖=‖gaussianPatternOperator z‖ := by
  apply finite_operator_duality
  intro x y
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (fun j => y j) ⬝ᵥ ((gaussianPatternArray z)ᵀ *ᵥ x)=
    x ⬝ᵥ ((gaussianPatternArray z) *ᵥ (fun j => y j))
  exact Matrix.dotProduct_transpose_mulVec _ _ _

lemma gaussianPatternOperator_spin {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (σ : Spin N) : gaussianPatternOperator z (fun i => spinValue (σ i))=gaussianPatternSum z σ := rfl

lemma gaussianPatternOperator_norm {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ‖gaussianPatternOperator z‖=Finset.univ.sup' Finset.univ_nonempty
      (fun σ : Spin N => ‖gaussianPatternSum z σ‖) := cube_operator_norm _

lemma gaussianPattern_max_sqrt {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Real.sqrt (2*gaussianPatternGroundEnergy 1 z)=‖gaussianPatternOperator z‖/N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : 2*gaussianPatternGroundEnergy 1 z=(‖gaussianPatternOperator z‖/N)^2 := by
    rw [gaussianPatternOperator_norm,gaussianPatternGroundEnergy,
      finite_sup_square (fun σ : Spin N => ‖gaussianPatternSum z σ‖) (fun _ => norm_nonneg _)
        (1/(2*N)) (by positivity)]
    field_simp
  rw [he,Real.sqrt_sq (div_nonneg (norm_nonneg _) (Nat.cast_nonneg N))]

lemma gaussianPattern_min_sqrt {N m : ℕ} (hN : 0 < N)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Real.sqrt (-2*gaussianPatternGroundEnergy (-1) z)=
      (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin N => ‖gaussianPatternSum z σ‖))/N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let M := Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin N => ‖gaussianPatternSum z σ‖)
  have hM : 0 ≤ M := Finset.le_inf' Finset.univ_nonempty (fun σ : Spin N => ‖gaussianPatternSum z σ‖) (fun σ _ => norm_nonneg _)
  have he : -2*gaussianPatternGroundEnergy (-1) z=(M/N)^2 := by
    unfold gaussianPatternGroundEnergy
    have hs := finite_sup_neg_square (fun σ : Spin N => ‖gaussianPatternSum z σ‖)
      (fun _ => norm_nonneg _) (1/(2*N)) (by positivity)
    simp only [neg_div]
    rw [hs]
    dsimp [M]
    field_simp
  rw [he,Real.sqrt_sq (div_nonneg hM (Nat.cast_nonneg N))]

end InvariantIsing

end

end OAI
