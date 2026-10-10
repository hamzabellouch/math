import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.TraceRays
import OAI.Analysis.JiangSu.Traces.CompletedSharedTrace

namespace OAI


noncomputable section
namespace NonunitalGamma
open Filter Topology TraceCone
open scoped ComplexOrder ENNReal NNReal CStarAlgebra

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] lemma finiteMatrixMap_apply (f : A →⋆ₙₐ[ℂ] B) (n : ℕ) (M : FinMatrix A n) (i j : Fin n) :
    finiteMatrixMap f n M i j=f (M i j) := rfl

@[simp] lemma stabilizationMap_stage (f : A →⋆ₙₐ[ℂ] B) (n : ℕ) (M : FinMatrix A n) :
    stabilizationMap f (matrixLimitStage n M)=matrixLimitStage n (finiteMatrixMap f n M) :=
  matrixLimitLift_stage _ (stabilizationCompatible f) n M

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma finiteMatrixMap_injective (f : A →⋆ₙₐ[ℂ] B) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (finiteMatrixMap f n) := by
  intro M N h
  ext i j
  exact hf (congrArg (fun Q : FinMatrix B n => Q i j) h)

lemma stabilizationMap_isometry (f : A →⋆ₙₐ[ℂ] B) (hf : Function.Injective f) :
    Isometry (stabilizationMap f) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  refine finiteMatrixSubalgebra_dense.induction_on x ?_ ?_
  · have hc : LipschitzWith 1 (stabilizationMap f) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
        NonUnitalStarAlgHom.norm_apply_le (stabilizationMap f) (x-y)
    exact isClosed_eq hc.continuous.norm continuous_norm
  · intro y
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective y
    change ‖stabilizationMap f (matrixLimitStage n M)‖=‖matrixLimitStage n M‖
    rw [stabilizationMap_stage,matrixLimitStage_norm,matrixLimitStage_norm]
    exact NonUnitalStarAlgHom.norm_map _ (finiteMatrixMap_injective f hf n) M

lemma stabilizationInr_isometry : Isometry (stabilizationInr (A := A)) :=
  stabilizationMap_isometry _ Unitization.inr_injective

lemma NormalizedTrace.stabilized_stage (τ : NormalizedTrace A) (n : ℕ) (a : Positive (FinMatrix A n)) :
    τ.stabilized (Positive.map (matrixLimitStage n) a)=
      (functionalWeight τ.functional τ.tracial).matrixTrace (Fin n) a := by
  change Pureness.sharedExtendedTrace τ.unitized
    (Positive.map stabilizationInr (Positive.map (matrixLimitStage n) a))=_
  have he : Positive.map stabilizationInr (Positive.map (matrixLimitStage n) a) =
      Positive.map (matrixLimitStage n)
        (Positive.map (finiteMatrixMap (Unitization.inrNonUnitalStarAlgHom ℂ A) n) a) := by
    apply Subtype.ext
    exact stabilizationMap_stage _ n a.1
  rw [he]
  rw [Pureness.sharedExtendedTrace_stage,Pureness.matrixTrace_apply,ExtendedTrace.matrixTrace_apply]
  change ENNReal.ofReal (∑ i : Fin n,τ.unitized.functional (Unitization.inr (a.1 i i))).re =
    ∑ i : Fin n, ENNReal.ofReal (τ.functional (a.1 i i)).re
  simp only [NormalizedTrace.unitized_inr,Complex.re_sum]
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro i _
  exact (τ.functional.map_nonneg (Positive.matrix_diagonal_nonneg a i)).1

lemma NormalizedTrace.stabilized_rank_stage (τ : NormalizedTrace A) (n : ℕ)
    (a : Positive (FinMatrix A n)) :
    τ.stabilized.rank (Positive.map (matrixLimitStage n) a)=
      ((functionalWeight τ.functional τ.tracial).matrixTrace (Fin n)).rank a := by
  rw [←ExtendedTrace.rank_pullback]
  have he : τ.stabilized.pullback (matrixLimitStage n)=
      (functionalWeight τ.functional τ.tracial).matrixTrace (Fin n) := by
    ext b
    exact τ.stabilized_stage n b
  rw [he]

end NonunitalGamma

end


noncomputable section
namespace NonunitalGamma
open Filter Topology TraceCone
open scoped ENNReal NNReal ComplexOrder CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] lemma scaledTrace_apply (r : ℝ≥0) (τ : ExtendedTrace A) (a : Positive A) :
    scaledTrace r τ a=(r:ℝ≥0∞)*τ a := rfl

lemma scaledTrace_rank (r : ℝ≥0) (τ : ExtendedTrace A) (a : Positive A) :
    (scaledTrace r τ).rank a=(r:ℝ≥0∞)*τ.rank a := by
  apply tendsto_nhds_unique ((scaledTrace r τ).tendsto_roots_rank_all a)
  exact (ENNReal.continuous_const_mul ENNReal.coe_ne_top).tendsto _ |>.comp
    (τ.tendsto_roots_rank_all a)

lemma boundedStabilized_stage (τ : ExtendedTrace A) (hτ : WeightBounded τ)
    (n : ℕ) (a : Positive (FinMatrix A n)) :
    boundedStabilized τ hτ (Positive.map (matrixLimitStage n) a)=τ.matrixTrace (Fin n) a := by
  classical
  by_cases h : τ=0
  · subst τ
    simp [boundedStabilized,ExtendedTrace.matrixTrace_apply]
  · rw [boundedStabilized,dite_eq_right h,scaledTrace_apply,NormalizedTrace.stabilized_stage,
      ExtendedTrace.matrixTrace_apply,ExtendedTrace.matrixTrace_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (normalizedWeight_ray τ hτ h (a.matrixDiagonal i)).symm

lemma boundedStabilized_rank_stage (τ : ExtendedTrace A) (hτ : WeightBounded τ)
    (n : ℕ) (a : Positive (FinMatrix A n)) :
    (boundedStabilized τ hτ).rank (Positive.map (matrixLimitStage n) a)=
      (τ.matrixTrace (Fin n)).rank a := by
  rw [←ExtendedTrace.rank_pullback]
  have he : (boundedStabilized τ hτ).pullback (matrixLimitStage n)=τ.matrixTrace (Fin n) := by
    ext b
    exact boundedStabilized_stage τ hτ n b
  rw [he]

lemma comparison_of_normalized_rank_lt (hcone : AllDenselyFiniteTracesBounded A)
    (hcmp : StrictComparison hcone) (a b : Positive (MatrixLimit A)) (hb : b.1 ≠ 0)
    (hgap : ∀ σ : NormalizedTrace A, σ.stabilized.rank a < σ.stabilized.rank b) :
    CuntzBelow a b := by
  apply hcmp a b hb
  intro τ hτ ht
  have hne : τ≠0 := by
    intro hz
    subst τ
    have hzero : boundedStabilized (0 : ExtendedTrace A) (hcone 0 hτ)=0 := by
      simp [boundedStabilized]
    rw [hzero] at ht
    have hr : (0 : ExtendedTrace (MatrixLimit A)).rank b=0 := by
      change liminf (fun _ : ℕ => (0 : ℝ≥0∞)) atTop=0
      simp
    rw [hr] at ht
    exact zero_ne_one ht
  let r := ‖positiveFunctionalCLM (boundedWeightFunctional τ (hcone τ hτ))‖₊
  let σ := normalizedWeight τ (hcone τ hτ) hne
  have hr : (r:ℝ≥0∞)≠0 := by
    exact_mod_cast (nnnorm_ne_zero_iff.mpr (boundedWeightFunctional_nonzero (hcone τ hτ) hne))
  rw [boundedStabilized,dite_eq_right hne,scaledTrace_rank] at ht ⊢
  rw [←ht]
  exact ENNReal.mul_lt_mul_right hr ENNReal.coe_ne_top (hgap σ)

end NonunitalGamma

end

end OAI
