import Mathlib
import OAI.Analysis.FreeWords.TensorUnitaryEnd

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators Matrix.Norms.L2Operator

open MeasureTheory

noncomputable section

instance matrixUnitaryMeasurable (d : ℕ) : MeasurableSpace (Matrix.unitaryGroup (Fin d) ℂ) := borel _

instance matrixUnitaryBorel (d : ℕ) : BorelSpace (Matrix.unitaryGroup (Fin d) ℂ) := ⟨rfl⟩

instance matrixUnitaryCompact (d : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin d) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  rw [Metric.isBounded_iff_subset_closedBall (0 : Matrix (Fin d) (Fin d) ℂ)]
  refine ⟨1,fun U hU => ?_⟩
  simp only [Metric.mem_closedBall,dist_zero_right]
  rcases subsingleton_or_nontrivial (Matrix (Fin d) (Fin d) ℂ) with h | h
  · simp [Subsingleton.elim U 0]
  · exact le_of_eq (CStarRing.norm_coe_unitary ⟨U,hU⟩)

def matrixHaar (d : ℕ) : Measure (Matrix.unitaryGroup (Fin d) ℂ) :=
  Measure.haarMeasure ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩

instance matrixHaar_probability (d : ℕ) : IsProbabilityMeasure (matrixHaar d) := by
  constructor
  exact Measure.haarMeasure_self

instance matrixHaar_leftInvariant (d : ℕ) : (matrixHaar d).IsMulLeftInvariant := by
  unfold matrixHaar
  infer_instance

theorem tensorMatrix_mul {r d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) :
    tensorMatrix (r := r) (U*V)=tensorMatrix U*tensorMatrix V := by
  classical
  ext a b
  simp only [tensorMatrix,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.prod_mul_distrib

theorem tensorMatrix_one {r d : ℕ} :
    tensorMatrix (r := r) (1 : Matrix (Fin d) (Fin d) ℂ)=1 := by
  classical
  ext a b
  simp only [tensorMatrix,Matrix.one_apply,prod_delta_eq]
  have he : (∀ t∈(Finset.univ : Finset (Fin r)), a t=b t) ↔ a=b := by simp [funext_iff]
  simp only [he]

theorem tensorMatrix_star {r d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    tensorMatrix (r := r) (star U)=star (tensorMatrix U) := by
  ext a b
  simp [tensorMatrix,Matrix.star_apply,star_prod]

theorem tensorMatrix_unitary {r d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    tensorMatrix (r := r) (U : Matrix (Fin d) (Fin d) ℂ) ∈
      Matrix.unitaryGroup (Fin r → Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff,← tensorMatrix_star,← tensorMatrix_mul]
  rw [Unitary.mul_star_self_of_mem U.property,tensorMatrix_one]

theorem continuous_tensorMatrix {r d : ℕ} :
    Continuous (tensorMatrix (r := r) (d := d)) := by
  unfold tensorMatrix
  fun_prop

def tensorAverage {r d : ℕ} (μ : Measure (Matrix.unitaryGroup (Fin d) ℂ))
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) :=
  ∫ U, tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
    star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)) ∂μ

theorem continuous_tensorConjugation {r d : ℕ}
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
        star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ))) := by
  exact ((continuous_tensorMatrix.comp continuous_subtype_val).mul continuous_const).mul
    (continuous_tensorMatrix.comp continuous_subtype_val).star

theorem tensorAverage_commute {r d : ℕ}
    (μ : Measure (Matrix.unitaryGroup (Fin d) ℂ)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) :
    Commute (tensorAverage μ T) (tensorMatrix (V : Matrix (Fin d) (Fin d) ℂ)) := by
  let S : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ := tensorMatrix (V : Matrix (Fin d) (Fin d) ℂ)
  have hint := (continuous_tensorConjugation T).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  have hint' := ((continuous_tensorConjugation T).mul (continuous_const (y := star S))).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  change Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
    tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
      star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ))*star S) μ at hint'
  have he : S*tensorAverage μ T*star S=tensorAverage μ T := by
    unfold tensorAverage
    rw [mul_assoc,← integral_mul_const_of_integrable hint,← integral_const_mul_of_integrable hint']
    have heq (U : Matrix.unitaryGroup (Fin d) ℂ) :
        S*(tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
          star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)))*star S =
        tensorMatrix ((V*U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)*T*
          star (tensorMatrix ((V*U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) := by
      change S*(tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
        star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)))*star S =
        tensorMatrix ((V : Matrix (Fin d) (Fin d) ℂ)*(U : Matrix (Fin d) (Fin d) ℂ))*T*
          star (tensorMatrix ((V : Matrix (Fin d) (Fin d) ℂ)*(U : Matrix (Fin d) (Fin d) ℂ)))
      simp only [tensorMatrix_mul,star_mul,S,mul_assoc]
    have hrewrite (U : Matrix.unitaryGroup (Fin d) ℂ) :=
      (mul_assoc S (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
        star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ))) (star S)).symm.trans (heq U)
    simp_rw [hrewrite]
    exact integral_mul_left_eq_self
      (fun U : Matrix.unitaryGroup (Fin d) ℂ => tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
        star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ))) V (μ := μ)
  have hu : star S*S=1 := Unitary.star_mul_self_of_mem (tensorMatrix_unitary V)
  have hh := congrArg (fun A => A*S) he
  change tensorAverage μ T*S=S*tensorAverage μ T
  simpa only [mul_assoc,hu,mul_one] using hh.symm

theorem tensorAverage_span (r d : ℕ) (hrd : r ≤ d)
    (μ : Measure (Matrix.unitaryGroup (Fin d) ℂ)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) :
    ∃ c : Equiv.Perm (Fin r) → ℂ, tensorAverage μ T=∑ π,c π • positionMatrix π := by
  exact unitary_tensor_commutant r d hrd _ (tensorAverage_commute μ T)

end

end KKWeingarten
end

end OAI
