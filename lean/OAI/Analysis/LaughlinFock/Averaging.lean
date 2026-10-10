import Mathlib
import OAI.Analysis.LaughlinFock.AveragedOperators
import OAI.Analysis.LaughlinFock.Rotations

namespace OAI

/-! Averaging. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexOrder
open NormedSpace MeasureTheory Topology
local instance averagingContinuousENorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

section
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
  (hX : ∀ s j, (X s j)ᴴ = -X s j)

local instance averagingRotationMeasurableSpace : MeasurableSpace (rotationGroup X hX) := borel _
local instance averagingRotationBorelSpace : BorelSpace (rotationGroup X hX) := ⟨rfl⟩

 

def rotationHaar : Measure (rotationGroup X hX) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (rotationGroup X hX))

instance rotationHaar_probability : IsProbabilityMeasure (rotationHaar X hX) :=
  ⟨by exact Measure.haarMeasure_self⟩

instance rotationHaar_leftInvariant : (rotationHaar X hX).IsMulLeftInvariant :=
  Measure.isMulLeftInvariant_haarMeasure _

 
def rotationEvaluation (j : J) : rotationGroup X hX →* Matrix (I j) (I j) ℂ where
  toFun g := (g.val j).val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem rotationEvaluation_continuous (j : J) : Continuous (rotationEvaluation X hX j) := by
  unfold rotationEvaluation
  exact continuous_subtype_val.comp ((continuous_apply j).comp continuous_subtype_val)

theorem rotationEvaluation_unitary (j : J) (g : rotationGroup X hX) :
    (rotationEvaluation X hX j g)ᴴ * rotationEvaluation X hX j g = 1 := by
  exact Unitary.star_mul_self_of_mem (g.val j).property

 

theorem rotationOrbit_integrable (j : J) (M : Matrix (I j) (I j) ℂ) :
    Integrable (fun g => rotationEvaluation X hX j g * M *
      (rotationEvaluation X hX j g)ᴴ) (rotationHaar X hX) := by
  have hc : Continuous (fun g => rotationEvaluation X hX j g * M *
      (rotationEvaluation X hX j g)ᴴ) :=
    ((rotationEvaluation_continuous X hX j).mul continuous_const).mul
      (rotationEvaluation_continuous X hX j).matrix_conjTranspose
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

 
def rotationAverage (j : J) (M : Matrix (I j) (I j) ℂ) : Matrix (I j) (I j) ℂ :=
  matrixConjugationAverage (rotationHaar X hX) (rotationEvaluation X hX j) M

theorem rotationAverage_posSemidef (j : J) (M : Matrix (I j) (I j) ℂ)
    (hM : M.PosSemidef) : (rotationAverage X hX j M).PosSemidef :=
  matrixConjugationAverage_posSemidef _ _ _ hM (rotationOrbit_integrable X hX j M)

theorem rotationAverage_trace (j : J) (M : Matrix (I j) (I j) ℂ) :
    (rotationAverage X hX j M).trace = M.trace :=
  matrixConjugationAverage_trace _ _ (rotationEvaluation_unitary X hX j) M
    (rotationOrbit_integrable X hX j M)

theorem rotationAverage_commutes (j : J) (M : Matrix (I j) (I j) ℂ)
    (g : rotationGroup X hX) :
    rotationAverage X hX j M * rotationEvaluation X hX j g =
      rotationEvaluation X hX j g * rotationAverage X hX j M :=
  matrixConjugationAverage_commutes _ _ (rotationEvaluation_unitary X hX j) M
    (rotationOrbit_integrable X hX j M) g

 

theorem rotationAverage_covariance {i j : J}
    (L : Matrix (I i) (I i) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ)
    (hL : ∀ s M, L (X s i * M - M * X s i) = X s j * L M - L M * X s j)
    (M : Matrix (I i) (I i) ℂ) :
    L (rotationAverage X hX i M) = rotationAverage X hX j (L M) := by
  unfold rotationAverage matrixConjugationAverage
  refine (L.toContinuousLinearMap.integral_comp_comm
    (rotationOrbit_integrable X hX i M)).symm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g => rotationGroup_covariance X hX L hL g M

theorem rotationAverage_one (j : J) :
    rotationAverage X hX j 1 = 1 := by
  have hU (g : rotationGroup X hX) :
      rotationEvaluation X hX j g * (rotationEvaluation X hX j g)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (g.val j).property
  simp [rotationAverage, matrixConjugationAverage, hU]

theorem rotationAverage_add (j : J) (M N : Matrix (I j) (I j) ℂ) :
    rotationAverage X hX j (M+N) = rotationAverage X hX j M + rotationAverage X hX j N := by
  simp only [rotationAverage, matrixConjugationAverage, Matrix.mul_add, Matrix.add_mul]
  exact integral_add (rotationOrbit_integrable X hX j M) (rotationOrbit_integrable X hX j N)

theorem rotationAverage_smul (j : J) (c : ℂ) (M : Matrix (I j) (I j) ℂ) :
    rotationAverage X hX j (c • M) = c • rotationAverage X hX j M := by
  simp only [rotationAverage, matrixConjugationAverage, Matrix.mul_smul, Matrix.smul_mul,
    integral_smul]

 
def rotationAverageLinear (j : J) : Matrix (I j) (I j) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ where
  toFun := rotationAverage X hX j
  map_add' := rotationAverage_add X hX j
  map_smul' := rotationAverage_smul X hX j

theorem rotationAverage_real_smul (j : J) (r : ℝ) (M : Matrix (I j) (I j) ℂ) :
    rotationAverage X hX j (r • M) = r • rotationAverage X hX j M :=
  (rotationAverageLinear X hX j).map_smul_of_tower r M

theorem rotationAverage_relative (j : J) (A H : Matrix (I j) (I j) ℂ) (r : ℝ)
    (h : (A + r • H).PosSemidef) :
    (rotationAverage X hX j A + r • rotationAverage X hX j H).PosSemidef := by
  have hp := rotationAverage_posSemidef X hX j (A+r•H) h
  rwa [rotationAverage_add, rotationAverage_real_smul] at hp

end
end LaughlinFock
end

end OAI
