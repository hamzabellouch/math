import OAI.Analysis.Pureness.Quasitrace.PositiveQuasitraceScaling
import OAI.Analysis.Pureness.Quasitrace.QuasitraceUltraproductAWEmbedding
import OAI.Analysis.Pureness.Quasitrace.QuasitraceScaledRank

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

def matrixStateUnitValue (n : ℕ) : ℝ :=
  finiteSpectralPositiveQuasitrace (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f)
    (n+1) ⟨1,zero_le_one⟩

lemma matrixStateUnitValue_pos (n : ℕ) : 0 < matrixStateUnitValue hsimple y hy f n :=
  regularizedState_positiveQuasitrace_faithful hsimple y hy f (n+1) ⟨1,zero_le_one⟩ one_ne_zero

def normalizedMatrixStatePositiveQuasitrace (n : ℕ) : PositiveQuasitrace (FinMatrix A (n+1)) :=
  (finiteSpectralPositiveQuasitrace (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) (n+1)).scale
    ⟨(matrixStateUnitValue hsimple y hy f n)⁻¹, inv_nonneg.mpr (matrixStateUnitValue_pos hsimple y hy f n).le⟩

lemma normalizedMatrixStatePositiveQuasitrace_unit (n : ℕ) :
    normalizedMatrixStatePositiveQuasitrace hsimple y hy f n ⟨1,zero_le_one⟩ = 1 :=
  inv_mul_cancel₀ (matrixStateUnitValue_pos hsimple y hy f n).ne'

lemma normalizedMatrixStatePositiveQuasitrace_metricSize_add (n : ℕ) (u v : FinMatrix A (n+1)) :
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n).metricSize (u+v) ≤
      (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n).metricSize u+
        (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n).metricSize v :=
  PositiveQuasitrace.scale_metricSize_add _ _
    (finiteSpectralPositiveQuasitrace_metricSize_add _ _ _ _ (n+1)) u v

lemma normalizedMatrixStatePositiveQuasitrace_sqrt_add (n : ℕ) (a b : Positive (FinMatrix A (n+1))) :
    Real.sqrt (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n (Positive.add a b)) ≤
      Real.sqrt (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n a)+
        Real.sqrt (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n b) :=
  PositiveQuasitrace.scale_sqrt_add _ _
    (finiteSpectralPositiveQuasitrace_sqrt_add _ _ _ _ (n+1)) a b

lemma normalizedMatrixStatePositiveQuasitrace_faithful (n : ℕ) (a : Positive (FinMatrix A (n+1)))
    (ha : a.1 ≠ 0) : 0 < normalizedMatrixStatePositiveQuasitrace hsimple y hy f n a :=
  mul_pos (inv_pos.mpr (matrixStateUnitValue_pos hsimple y hy f n))
    (regularizedState_positiveQuasitrace_faithful hsimple y hy f (n+1) a ha)

lemma normalizedMatrixStatePositiveQuasitrace_root_rank (n : ℕ) (a : Positive (FinMatrix A (n+1))) :
    Tendsto (fun k => ENNReal.ofReal
      (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n (Positive.power (Positive.rootExponent k) a)))
      atTop (nhds (ENNReal.ofReal (matrixStateUnitValue hsimple y hy f n)⁻¹ *
        regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass (n+1) a))) := by
  have ht := finiteSpectralPositiveQuasitrace_root_rank
    (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) (n+1) a
  have hm := (ENNReal.continuous_const_mul (a := ENNReal.ofReal (matrixStateUnitValue hsimple y hy f n)⁻¹)
    ENNReal.ofReal_ne_top).continuousAt.tendsto.comp ht
  have he (k : ℕ) : ENNReal.ofReal
      (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n (Positive.power (Positive.rootExponent k) a)) =
      ENNReal.ofReal (matrixStateUnitValue hsimple y hy f n)⁻¹ * ENNReal.ofReal
        (finiteSpectralPositiveQuasitrace (regularizedFiniteDimension f.toAddHom f.monotone)
          (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
          (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) (n+1)
          (Positive.power (Positive.rootExponent k) a)) :=
    ENNReal.ofReal_mul (inv_nonneg.mpr (matrixStateUnitValue_pos hsimple y hy f n).le)
  simp only [he]
  exact hm

variable (U : Ultrafilter ℕ)

abbrev NormalizedMatrixStateUltraproduct :=
  FilteredQuasitraceQuotient (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) (U : Filter ℕ)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)

abbrev NormalizedMatrixStateUltraAW :=
  UltralimitAWCompletion (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)

def normalizedMatrixStateUltraEmbedding :
    NormalizedMatrixStateUltraproduct hsimple y hy f U →⋆ₐ[ℂ] NormalizedMatrixStateUltraAW hsimple y hy f U :=
  ultraproductAWEmbedding _ _ _ _

theorem normalizedMatrixStateUltra_finite_awstar :
    Function.Injective (normalizedMatrixStateUltraEmbedding hsimple y hy f U) ∧
    (∀ x : NormalizedMatrixStateUltraproduct hsimple y hy f U, star x*x=1 → x*star x=1) ∧
    (∀ S : Set (NormalizedMatrixStateUltraAW hsimple y hy f U),
      ∃ p : NormalizedMatrixStateUltraAW hsimple y hy f U, IsStarProjection p ∧
        ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z) ∧
    (∃ Q : ComplexQuasitrace (NormalizedMatrixStateUltraAW hsimple y hy f U),
      Q 1=1 ∧ ∀ x, Q (star x*x)=0 ↔ x=0) := by
  refine ⟨ultraproductAWEmbedding_injective _ _ _ _, ?_, ?_, ?_⟩
  · exact filteredQuasitraceQuotient_finite _ _ _ _ (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
  · exact ultralimitAWCompletion_annihilator _ _ _ _ (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
  · refine ⟨ultralimitAWQuasitrace _ _ _ _ (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f), ?_, ?_⟩
    · exact ultralimitAWQuasitrace_unit _ _ _ _ _
    · exact ultralimitAWQuasitrace_faithful _ _ _ _ _
end CuntzPureness

end

end OAI
