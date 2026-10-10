import OAI.InformationTheory.Entanglement.DensityChange

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory
namespace SecretKey
open ChannelCompletion
variable {n : Type} [Fintype n] [DecidableEq n]
lemma traceNorm_eq_zero (A : Mat n) : traceNorm A=0 ↔ A=0 := by
  constructor
  · intro h
    have hs : CFC.sqrt (Aᴴ*A)=0 := by
      apply (sqrt_psd (Aᴴ*A)).trace_eq_zero_iff.mp
      apply Complex.ext
      · exact h
      · exact (Complex.nonneg_iff.mp (sqrt_psd (Aᴴ*A)).trace_nonneg).2.symm
    have he := CFC.sqrt_mul_sqrt_self (Aᴴ*A) (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
    rw [hs,zero_mul] at he
    exact Matrix.conjTranspose_mul_self_eq_zero.mp he.symm
  · rintro rfl
    simp [traceNorm]
lemma traceNorm_real_smul (c : ℝ) (A : Mat n) :
    traceNorm (c • A)= |c| *traceNorm A := by
  by_cases hc : 0≤c
  · have he : c • A=(c : ℂ) • A := by ext i j; simp
    rw [he,traceNorm_smul_nonneg c hc,abs_of_nonneg hc]
  · have hn : 0≤-c := by linarith
    have he : c • A=-((-c) • A) := by simp
    rw [he,traceNorm_neg]
    have he' : (-c) • A=((-c) : ℂ) • A := by ext i j; simp
    rw [he',abs_of_nonpos (le_of_not_ge hc)]
    simpa only [Complex.ofReal_neg] using traceNorm_smul_nonneg (-c) hn A

@[ext] structure TraceMatrix (n : Type) where
  val : Matrix n n ℂ
namespace TraceMatrix
def toEquiv : TraceMatrix n ≃ Mat n where
  toFun := val
  invFun := mk
  left_inv := by intro A; cases A; rfl
  right_inv := fun _ => rfl
instance traceMatrixAddCommGroup : AddCommGroup (TraceMatrix n) := toEquiv.addCommGroup
instance traceMatrixModule : Module ℝ (TraceMatrix n) := toEquiv.addEquiv.module ℝ
def equiv : TraceMatrix n ≃ₗ[ℝ] Mat n := toEquiv.addEquiv.linearEquiv ℝ
instance traceMatrixNormedAddCommGroup : NormedAddCommGroup (TraceMatrix n) := AddGroupNorm.toNormedAddCommGroup
  { toFun := fun A => traceNorm A.val
    map_zero' := (traceNorm_eq_zero 0).mpr rfl
    neg' := fun A => traceNorm_neg A.val
    add_le' := fun A B => traceNorm_add_le A.val B.val
    eq_zero_of_map_eq_zero' := fun A h => toEquiv.injective ((traceNorm_eq_zero A.val).mp h) }
lemma norm_eq (A : TraceMatrix n) : ‖A‖=traceNorm A.val := rfl
instance traceMatrixNormedSpace : NormedSpace ℝ (TraceMatrix n) where
  norm_smul_le c A := by
    change traceNorm (c • A.val)≤‖c‖*traceNorm A.val
    rw [traceNorm_real_smul,Real.norm_eq_abs]
instance traceMatrixFiniteDimensional : FiniteDimensional ℝ (TraceMatrix n) := equiv.symm.finiteDimensional
instance traceMatrixCompleteSpace : CompleteSpace (TraceMatrix n) := FiniteDimensional.complete ℝ _
def equivL : TraceMatrix n ≃L[ℝ] Mat n := equiv.toContinuousLinearEquiv
instance traceMatrixMeasurableSpace : MeasurableSpace (TraceMatrix n) := borel _
instance traceMatrixBorelSpace : BorelSpace (TraceMatrix n) := ⟨rfl⟩
instance traceMatrixSecondCountableTopology : SecondCountableTopology (TraceMatrix n) := by
  have : ProperSpace (TraceMatrix n) := FiniteDimensional.proper ℝ _
  infer_instance
lemma measurable_into {T : Type*} [MeasurableSpace T] {D : T → Mat n}
    (hD : Measurable D) : Measurable (fun t => TraceMatrix.mk (D t)) :=
  equivL.symm.continuous.measurable.comp hD
lemma integrable_into {T : Type*} [MeasurableSpace T] {μ : Measure T} {D : T → Mat n}
    (hD : ∀ i j, Integrable (fun t => D t i j) μ) :
    Integrable (fun t => TraceMatrix.mk (D t)) μ := by
  let B (i j : n) : ℂ →ₗ[ℝ] Mat n :=
    { toFun := fun c => Matrix.single i j c
      map_add' := fun x y => Matrix.single_add _ _ _ _
      map_smul' := fun c x => by simp }
  have hb (i j : n) : Integrable (fun t => Matrix.single i j (D t i j)) μ :=
    (B i j).toContinuousLinearMap.integrable_comp (hD i j)
  have hi : Integrable D μ := by
    have h := integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hb i j))
    have he : (fun t => ∑ i, ∑ j, Matrix.single i j (D t i j))=D := by
      funext t
      exact (Matrix.matrix_eq_sum_single (D t)).symm
    rwa [he] at h
  exact equivL.symm.toContinuousLinearMap.integrable_comp hi
lemma setIntegral_entry {T : Type*} [MeasurableSpace T] {μ : Measure T} {D : T → Mat n}
    (hD : ∀ i j, Integrable (fun t => D t i j) μ) (s : Set T) (i j : n) :
    (∫ t in s, TraceMatrix.mk (D t) ∂μ).val i j=∫ t in s, D t i j ∂μ := by
  let f : TraceMatrix n →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj i).comp equivL.toContinuousLinearMap)
  exact (f.integral_comp_comm (integrable_into hD).integrableOn).symm
end TraceMatrix

end SecretKey

end

end OAI
