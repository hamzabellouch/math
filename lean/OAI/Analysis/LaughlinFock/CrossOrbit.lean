import Mathlib
import OAI.Analysis.LaughlinFock.FockRotations
import OAI.Analysis.LaughlinFock.RectangularOrbit

namespace OAI

/-! Cross Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexOrder
open MeasureTheory Topology
local instance crossOrbitContinuousENorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

section
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
  (hX : ∀ s j, (X s j)ᴴ = -X s j)
local instance crossOrbitRotationMeasurableSpace : MeasurableSpace (rotationGroup X hX) := borel _
local instance crossOrbitRotationBorelSpace : BorelSpace (rotationGroup X hX) := ⟨rfl⟩

 
def rotationCrossAverage (i j : J) (M : Matrix (I i) (I j) ℂ) : Matrix (I i) (I j) ℂ :=
  ∫ g, rotationEvaluation X hX i g * M * (rotationEvaluation X hX j g)ᴴ ∂rotationHaar X hX

theorem rotationCrossOrbit_integrable (i j : J) (M : Matrix (I i) (I j) ℂ) :
    Integrable (fun g => rotationEvaluation X hX i g * M * (rotationEvaluation X hX j g)ᴴ)
      (rotationHaar X hX) := by
  have hc : Continuous (fun g => rotationEvaluation X hX i g * M *
      (rotationEvaluation X hX j g)ᴴ) :=
    ((rotationEvaluation_continuous X hX i).matrix_mul continuous_const).matrix_mul
      (rotationEvaluation_continuous X hX j).matrix_conjTranspose
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

 
theorem rotationCrossAverage_invariant (i j : J) (M : Matrix (I i) (I j) ℂ)
    (h : rotationGroup X hX) :
    rotationEvaluation X hX i h * rotationCrossAverage X hX i j M *
      (rotationEvaluation X hX j h)ᴴ = rotationCrossAverage X hX i j M := by
  unfold rotationCrossAverage
  rw [matrixIntegral_mul_left_right _ (rotationCrossOrbit_integrable X hX i j M)]
  calc
    _ = ∫ g, rotationEvaluation X hX i (h*g) * M * (rotationEvaluation X hX j (h*g))ᴴ
          ∂rotationHaar X hX := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        simp only [map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ:=rotationHaar X hX)
      (fun g => rotationEvaluation X hX i g * M * (rotationEvaluation X hX j g)ᴴ) h

theorem rotationCrossAverage_intertwines (i j : J) (M : Matrix (I i) (I j) ℂ)
    (h : rotationGroup X hX) :
    rotationEvaluation X hX i h * rotationCrossAverage X hX i j M =
      rotationCrossAverage X hX i j M * rotationEvaluation X hX j h := by
  have he := congrArg (fun A => A * rotationEvaluation X hX j h)
    (rotationCrossAverage_invariant X hX i j M h)
  simpa only [Matrix.mul_assoc, rotationEvaluation_unitary, Matrix.mul_one] using he

 

theorem rotationCrossAverage_intertwines_generator (i j : J) (M : Matrix (I i) (I j) ℂ)
    (s : σ) : X s i * rotationCrossAverage X hX i j M =
      rotationCrossAverage X hX i j M * X s j := by
  apply matrix_intertwiner_generator_of_flow
  intro t
  exact rotationCrossAverage_intertwines X hX i j M
    ⟨rotationFlow X hX s t, rotationFlow_mem_group X hX s t⟩

 

theorem rotationAverage_mixed_sandwich {i j k : J}
    (C : Matrix (I k) (I i) ℂ) (D : Matrix (I k) (I j) ℂ)
    (hC : ∀ s, X s k*C = C*X s i) (hD : ∀ s, X s k*D = D*X s j)
    (M : Matrix (I i) (I j) ℂ) :
    rotationAverage X hX k (C*M*Dᴴ) = C * rotationCrossAverage X hX i j M * Dᴴ := by
  unfold rotationAverage matrixConjugationAverage rotationCrossAverage
  rw [matrixIntegral_mul_left_right _ (rotationCrossOrbit_integrable X hX i j M)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  have hc := rotationGroup_intertwiner X hX C hC g
  have hd : Dᴴ * (rotationEvaluation X hX k g)ᴴ =
      (rotationEvaluation X hX j g)ᴴ * Dᴴ := by
    have he := congrArg Matrix.conjTranspose (rotationGroup_intertwiner X hX D hD g)
    simp only [Matrix.conjTranspose_mul] at he
    exact he
  change rotationEvaluation X hX k g*C = C*rotationEvaluation X hX i g at hc
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (rotationEvaluation X hX k g) C, hc]
  simp only [Matrix.mul_assoc, hd]

end

 
theorem spinRotationCrossAverage_zero {Q n m : ℕ} (hnm : n ≠ m)
    (M : Matrix (Fin (n+1)) (Fin (m+1)) ℂ) :
    rotationCrossAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q)
      (.spin n) (.spin m) M = 0 := by
  apply spin_intertwiner_zero_of_ne hnm
  intro s
  exact rotationCrossAverage_intertwines_generator
    (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.spin n) (.spin m) M s

 

theorem sectorAverage_spin_mixed_sandwich {Q k n : ℕ}
    (C D : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s)*C = C*spinGenerator n s)
    (hD : ∀ s, sectorOneBody Q k (spinGenerator Q s)*D = D*spinGenerator n s)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    sectorAverage Q k (C*M*Dᴴ) = (M.trace / (n+1 : ℂ)) • (C*Dᴴ) := by
  have h := rotationAverage_mixed_sandwich (fockRotationGenerator Q)
    (fockRotationGenerator_skew Q) (i:=.spin n) (j:=.spin n) (k:=.sector k) C D hC hD M
  change sectorAverage Q k (C*M*Dᴴ) = C * rotationAverage (fockRotationGenerator Q)
    (fockRotationGenerator_skew Q) (.spin n) M * Dᴴ at h
  rw [h, spinRotationAverage]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

 
theorem sectorAverage_spin_cross_sandwich {Q k n m : ℕ} (hnm : n ≠ m)
    (C : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (D : Matrix (SectorOccupation Q k) (Fin (m+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s)*C = C*spinGenerator n s)
    (hD : ∀ s, sectorOneBody Q k (spinGenerator Q s)*D = D*spinGenerator m s)
    (M : Matrix (Fin (n+1)) (Fin (m+1)) ℂ) :
    sectorAverage Q k (C*M*Dᴴ) = 0 := by
  have h := rotationAverage_mixed_sandwich (fockRotationGenerator Q)
    (fockRotationGenerator_skew Q) (i:=.spin n) (j:=.spin m) (k:=.sector k) C D hC hD M
  rw [spinRotationCrossAverage_zero hnm, Matrix.mul_zero, Matrix.zero_mul] at h
  exact h

 
theorem fockAverage_spin_mixed_sandwich {Q k n : ℕ}
    (C D : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s)*C = C*spinGenerator n s)
    (hD : ∀ s, sectorOneBody Q k (spinGenerator Q s)*D = D*spinGenerator n s)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    fockAverage Q (exteriorLift Q k (C*M*Dᴴ)) =
      (M.trace / (n+1 : ℂ)) • exteriorLift Q k (C*Dᴴ) := by
  rw [fockAverage_exteriorLift, sectorAverage_spin_mixed_sandwich C D hC hD]
  exact (exteriorLiftLinear Q k).map_smul _ _

end LaughlinFock
end

end OAI
