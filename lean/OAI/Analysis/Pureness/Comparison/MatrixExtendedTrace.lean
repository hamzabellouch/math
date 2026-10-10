import OAI.Analysis.Pureness.Comparison.MatrixTraceValues
import OAI.Analysis.Pureness.Comparison.MatrixTraceCompression

namespace OAI
noncomputable section
open scoped CStarAlgebra ComplexOrder ENNReal Topology
open Filter
namespace CuntzComparison
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma compression_starMul_stage (m : ℕ) (x : MatrixLimit A) :
    Positive.starMul (matrixCompression m x) =
      Positive.map (matrixLimitStage m) (Positive.starMul (matrixCornerExtract m x)) := by
  apply Subtype.ext
  change star (matrixCompression m x) * matrixCompression m x =
    matrixLimitStage m (star (matrixCornerExtract m x) * matrixCornerExtract m x)
  rw [map_mul, map_star, matrixCornerExtract_spec]

lemma compression_mulStar_stage (m : ℕ) (x : MatrixLimit A) :
    Positive.mulStar (matrixCompression m x) =
      Positive.map (matrixLimitStage m) (Positive.mulStar (matrixCornerExtract m x)) := by
  apply Subtype.ext
  change matrixCompression m x * star (matrixCompression m x) =
    matrixLimitStage m (matrixCornerExtract m x * star (matrixCornerExtract m x))
  rw [map_mul, map_star, matrixCornerExtract_spec]

namespace TracialState
lemma matrixTraceValue_compression_tracial (τ : TracialState A) (m : ℕ) (x : MatrixLimit A) :
    τ.matrixTraceValue (Positive.starMul (matrixCompression m x)) =
      τ.matrixTraceValue (Positive.mulStar (matrixCompression m x)) := by
  rw [compression_starMul_stage, compression_mulStar_stage, τ.matrixTraceValue_stage, τ.matrixTraceValue_stage]
  exact (τ.extendedTrace.matrixTrace (Fin m)).tracial _

lemma matrixTraceValue_compression_eq_corner (τ : TracialState A) (m : ℕ) (x : MatrixLimit A) :
    τ.matrixTraceValue (Positive.mulStar (matrixCompression m x)) =
      τ.cornerTraceValue m (Positive.mulStar (matrixCompression m x)) := by
  rw [compression_mulStar_stage, τ.matrixTraceValue_stage, τ.cornerTraceValue_stage_large le_rfl]

lemma matrixTraceValue_compression_bound (τ : TracialState A) (m : ℕ) (x : MatrixLimit A) :
    τ.matrixTraceValue (Positive.mulStar (matrixCompression m x)) ≤ τ.matrixTraceValue (Positive.mulStar x) := by
  rw [τ.matrixTraceValue_compression_eq_corner]
  calc
    _ ≤ τ.cornerTraceValue m (Positive.mulStar x) :=
      ENNReal.ofReal_le_ofReal (τ.matrixCornerFunctional_mulStar_bound m x)
    _ ≤ _ := le_iSup (fun n => τ.cornerTraceValue n (Positive.mulStar x)) m

lemma matrixTraceValue_tracial_le (τ : TracialState A) (x : MatrixLimit A) :
    τ.matrixTraceValue (Positive.starMul x) ≤ τ.matrixTraceValue (Positive.mulStar x) := by
  apply iSup_le
  intro n
  have hc : Tendsto (fun m => Positive.starMul (matrixCompression m x)) atTop (𝓝 (Positive.starMul x)) := by
    rw [tendsto_subtype_rng]
    exact (matrixCompression_tendsto x).star.mul (matrixCompression_tendsto x)
  have ht := (τ.cornerTraceValue_continuous n).tendsto (Positive.starMul x) |>.comp hc
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro m
  calc
    _ ≤ τ.matrixTraceValue (Positive.starMul (matrixCompression m x)) :=
      le_iSup (fun k => τ.cornerTraceValue k _) n
    _ = τ.matrixTraceValue (Positive.mulStar (matrixCompression m x)) := τ.matrixTraceValue_compression_tracial m x
    _ ≤ _ := τ.matrixTraceValue_compression_bound m x

theorem matrixTraceValue_tracial (τ : TracialState A) (x : MatrixLimit A) :
    τ.matrixTraceValue (Positive.starMul x) = τ.matrixTraceValue (Positive.mulStar x) := by
  apply le_antisymm (τ.matrixTraceValue_tracial_le x)
  have h := τ.matrixTraceValue_tracial_le (star x)
  have h₁ : Positive.starMul (star x) = Positive.mulStar x := Subtype.ext (by simp [Positive.starMul, Positive.mulStar])
  have h₂ : Positive.mulStar (star x) = Positive.starMul x := Subtype.ext (by simp [Positive.starMul, Positive.mulStar])
  rwa [h₁,h₂] at h

def matrixExtendedTrace (τ : TracialState A) : ExtendedTrace (MatrixLimit A) where
  toFun := τ.matrixTraceValue
  map_zero := τ.matrixTraceValue_zero
  map_add := τ.matrixTraceValue_add
  map_smul := τ.matrixTraceValue_smul
  tracial := τ.matrixTraceValue_tracial
  lowerSemicontinuous := τ.matrixTraceValue_lowerSemicontinuous

@[simp] theorem matrixExtendedTrace_stage (τ : TracialState A) (m : ℕ) (a : Positive (FinMatrix A m)) :
    τ.matrixExtendedTrace (Positive.map (matrixLimitStage m) a) = τ.extendedTrace.matrixTrace (Fin m) a :=
  τ.matrixTraceValue_stage m a

theorem matrixExtendedTrace_pullback (τ : TracialState A) (m : ℕ) :
    τ.matrixExtendedTrace.pullback (matrixLimitStage m) = τ.extendedTrace.matrixTrace (Fin m) := by
  ext a
  exact τ.matrixExtendedTrace_stage m a

theorem matrixExtendedTrace_rank_stage (τ : TracialState A) (m : ℕ) (a : Positive (FinMatrix A m)) :
    τ.matrixExtendedTrace.rank (Positive.map (matrixLimitStage m) a) = (τ.extendedTrace.matrixTrace (Fin m)).rank a := by
  rw [← ExtendedTrace.rank_pullback, τ.matrixExtendedTrace_pullback]
end TracialState
end CuntzComparison

end

end OAI
