import OAI.Analysis.Pureness.Comparison.MatrixCornerFunctionals

namespace OAI
noncomputable section
open scoped CStarAlgebra ComplexOrder ENNReal NNReal Topology
namespace CuntzComparison
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace TracialState

def cornerTraceValue (τ : TracialState A) (n : ℕ) (a : Positive (MatrixLimit A)) : ℝ≥0∞ :=
  ENNReal.ofReal (τ.matrixCornerFunctional n a.1).re

lemma cornerTraceValue_nonneg_re (τ : TracialState A) (n : ℕ) (a : Positive (MatrixLimit A)) :
    0 ≤ (τ.matrixCornerFunctional n a.1).re :=
  (Complex.nonneg_iff.mp ((τ.matrixCornerFunctional n).map_nonneg a.2)).1

lemma cornerTraceValue_monotone (τ : TracialState A) (a : Positive (MatrixLimit A)) :
    Monotone (fun n => τ.cornerTraceValue n a) :=
  ENNReal.ofReal_mono.comp (τ.matrixCornerFunctional_monotone a.2)

lemma cornerTraceValue_continuous (τ : TracialState A) (n : ℕ) : Continuous (τ.cornerTraceValue n) :=
  ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp
    ((map_continuous (τ.matrixCornerFunctional n)).comp continuous_subtype_val))

@[simp] lemma cornerTraceValue_zero (τ : TracialState A) (n : ℕ) : τ.cornerTraceValue n Positive.zero = 0 := by
  change ENNReal.ofReal ((τ.matrixCornerFunctional n) 0).re = 0
  rw [map_zero]
  simp

lemma cornerTraceValue_add (τ : TracialState A) (n : ℕ) (a b : Positive (MatrixLimit A)) :
    τ.cornerTraceValue n (Positive.add a b) = τ.cornerTraceValue n a + τ.cornerTraceValue n b := by
  change ENNReal.ofReal ((τ.matrixCornerFunctional n) (a.1+b.1)).re = _
  rw [map_add, Complex.add_re, ENNReal.ofReal_add (τ.cornerTraceValue_nonneg_re n a)
    (τ.cornerTraceValue_nonneg_re n b)]
  rfl

lemma cornerTraceValue_smul (τ : TracialState A) (n : ℕ) (r : ℝ≥0) (a : Positive (MatrixLimit A)) :
    τ.cornerTraceValue n (Positive.smul r a) = (r : ℝ≥0∞) * τ.cornerTraceValue n a := by
  change ENNReal.ofReal ((τ.matrixCornerFunctional n) ((r : ℝ) • a.1)).re = _
  rw [← Complex.coe_smul, map_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ = ENNReal.ofReal (r : ℝ) * ENNReal.ofReal (τ.matrixCornerFunctional n a.1).re := ENNReal.ofReal_mul r.2
    _ = _ := by rw [ENNReal.ofReal_coe_nnreal]; rfl

def matrixTraceValue (τ : TracialState A) (a : Positive (MatrixLimit A)) : ℝ≥0∞ :=
  ⨆ n : ℕ, τ.cornerTraceValue n a

lemma matrixTraceValue_lowerSemicontinuous (τ : TracialState A) : LowerSemicontinuous τ.matrixTraceValue :=
  lowerSemicontinuous_iSup (fun n => (τ.cornerTraceValue_continuous n).lowerSemicontinuous)

@[simp] lemma matrixTraceValue_zero (τ : TracialState A) : τ.matrixTraceValue Positive.zero = 0 := by
  simp [matrixTraceValue]

lemma matrixTraceValue_add (τ : TracialState A) (a b : Positive (MatrixLimit A)) :
    τ.matrixTraceValue (Positive.add a b) = τ.matrixTraceValue a + τ.matrixTraceValue b := by
  simp only [matrixTraceValue, cornerTraceValue_add]
  exact (ENNReal.iSup_add_iSup_of_monotone (τ.cornerTraceValue_monotone a) (τ.cornerTraceValue_monotone b)).symm

lemma matrixTraceValue_smul (τ : TracialState A) (r : ℝ≥0) (a : Positive (MatrixLimit A)) :
    τ.matrixTraceValue (Positive.smul r a) = (r : ℝ≥0∞) * τ.matrixTraceValue a := by
  simp only [matrixTraceValue, cornerTraceValue_smul, ENNReal.mul_iSup]

lemma cornerTraceValue_stage_large (τ : TracialState A) {n m : ℕ} (h : m ≤ n) (a : Positive (FinMatrix A m)) :
    τ.cornerTraceValue n (Positive.map (matrixLimitStage m) a) = τ.extendedTrace.matrixTrace (Fin m) a := by
  change ENNReal.ofReal (τ.matrixTraceLinear (matrixCornerExtract n (matrixLimitStage m a.1))).re = _
  rw [matrixCornerExtract_stage_large h]
  calc
    _ = τ.extendedTrace.matrixTrace (Fin n) (Positive.map (matrixInclusion h) a) := (τ.extended_matrixTrace _).symm
    _ = _ := matrixInclusion_trace τ.extendedTrace h a

theorem matrixTraceValue_stage (τ : TracialState A) (m : ℕ) (a : Positive (FinMatrix A m)) :
    τ.matrixTraceValue (Positive.map (matrixLimitStage m) a) = τ.extendedTrace.matrixTrace (Fin m) a := by
  apply le_antisymm
  · apply iSup_le
    intro n
    rcases le_total m n with h | h
    · exact (τ.cornerTraceValue_stage_large h a).le
    · calc
        _ ≤ τ.cornerTraceValue m (Positive.map (matrixLimitStage m) a) :=
          τ.cornerTraceValue_monotone _ h
        _ = _ := τ.cornerTraceValue_stage_large le_rfl a
  · rw [← τ.cornerTraceValue_stage_large (n := m) le_rfl a]
    exact le_iSup (fun n => τ.cornerTraceValue n _) m
end TracialState
end CuntzComparison

end

end OAI
