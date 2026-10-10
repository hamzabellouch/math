import OAI.Combinatorics.Progressions.Geometry.AllocatedOriginalCoarseBoxSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p cEarly cLate P e E : ℝ}

local notation "Eraw" => (E + 2) + 4

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "accuracy" => allocatedOriginalCoverAccuracy P (E + 2)
local notation "pAccuracy" => allocatedCommonRefinedSourceLog m p cEarly P e 0 accuracy
local notation "pSampling" => allocatedCommonRefinedSourceLog m p cLate P e Eraw accuracy
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p cLate P e Eraw
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m pAccuracy e
local notation "resourceLog" => allocatedFullGridPrimitiveResourceLog m pAccuracy maskLog profileLog accuracy
local notation "tolerance" => allocatedSitePrimitiveTolerance m pAccuracy maskLog profileLog accuracy

local notation "D" => allocatedComparisonDimension m p
local notation "pNum" => allocatedCommonScaleNumeric m p cLate P Eraw
local notation "error" => allocatedReferenceIdealError m D P Eraw
local notation "lengthLog" => allocatedIdealScaleLog m D pNum e maskLog error
local notation "gainLog" => allocatedProfileGainLog m D P maskLog
local notation "Pbase" => allocatedIdealSourceBudget m D pNum e maskLog error
local notation "lateLog" => allocatedSpatialLateLog (G := G) B Pbase Pbase
local notation "rawFourier" => allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_original_common_genuine_box_source
    (hp : 0 ≤ p) (hcEarly : 0 ≤ cEarly) (hcLate : 0 ≤ cLate) (hEarlyLate : cEarly ≤ cLate)
    (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1) (hmP : ((m + 2 : ℕ) : ℝ) ≤ P) (hpP : p ≤ P)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p)
    (hR1 : ∀ j, R j ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp cEarly) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp cLate)
    (hBlocks : ∀ (j : Fin m) (i : Fin (n j)), max
      (positiveModerateSpectrumBlockCount j.val (rowSets j).card
        ((layerTailDegree m + 2) * (rowSets j).card))
      (uniformSpectrumBlockCount j.val (rowSets j).card ((j.val + 1) * (rowSets j).card)) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e)
    {A T Kproj Kideal Ksite Knorm : ℕ} (hT : 1 ≤ T) (hKsite : 2 ≤ Ksite)
    (hKnorm : 1 ≤ Knorm)
    (hnorm : AllocatedSourceNarrowNormalization.{uG,uI,uB,uJ,uX} m Knorm)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B U b hR hσ D P (E + 2) e pNum δ A T Kproj Kideal) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp resourceLog) (Real.exp resourceLog) (Real.exp resourceLog)
        ⟨Real.exp resourceLog, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      ∀ (Dgeom cgeom : ℝ) (Kgen : ℕ) (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η),
        AllocatedOriginalGenuineAffineData.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S P E e pNum Pbase
          (allocatedSourceSamplingBudget m dim A Pbase (E + 2) lateLog rawFourier)
          pAccuracy pSampling Dgeom cgeom resourceLog hP δ A
          (max T (max Kproj Kideal)) (max Ksite Knorm) Kgen witnesses
          M Dwin hM hDwin η hη := by
  obtain ⟨witnesses, hBounds, hWitnesses, hData⟩ :=
    exists_original_common_coarse_box_source B U b hR hσ hp hcEarly hcLate hEarlyLate hP he hE
      hdimSmall hmP hpP hvars hI hn hJ hR1 hσ1 hRi hσi hBlocks hδ hδ1 hδe
      hT hKsite hKnorm hnorm hSampling hraw
  refine ⟨witnesses, hBounds, hWitnesses, ?_⟩
  intro Dgeom cgeom Kgen M Dwin hM hDwin η hη
  exact allocatedOriginalGenuineAffineData_of_coarse B U b hR hσ S hP witnesses hBounds
    M Dwin hM hDwin η hη (hData M Dwin hM hDwin η hη)

end Erdos3.VectorPolynomial

end

end OAI
