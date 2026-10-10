import OAI.Combinatorics.Progressions.Estimates.AllocatedFixedCommonCover
import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridCoefficientBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {Psp E e pAccuracy pSampling : ℝ}

local notation "maskLog" => allocatedSiteKernelMaskLog m Psp
local notation "profileLog" => allocatedIdealProfileLog m pAccuracy e
local notation "accuracy" => allocatedOriginalCoverAccuracy Psp (E + 1)
local notation "tolerance" => allocatedSitePrimitiveTolerance m pAccuracy maskLog profileLog accuracy
local notation "cutoff" => allocatedRefinedPeriodCutoff m Psp

theorem allocatedProductSeparatedUniformSourceContract_of_sampling
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (hpAccuracy : 0 ≤ pAccuracy)
    (hAccuracySampling : pAccuracy ≤ pSampling)
    (hmP : ((m + 1 : ℕ) : ℝ) ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pAccuracy)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pAccuracy) (hn : ∀ j, (n j : ℝ) ≤ pAccuracy)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pAccuracy)
    (hcutoff : (cutoff : ℝ) ≤ Real.exp pAccuracy) (hS : (S.value : ℝ) ≤ Real.exp pSampling)
    (hEbudget : accuracy + 4 ≤ pAccuracy)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val)
    (hWitness : ∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) :
    AllocatedProductSeparatedUniformSourceContract.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ S Psp E e pAccuracy pSampling hPsp witnesses := by
  unfold AllocatedProductSeparatedUniformSourceContract
  intro o X _ _ M modulus hM hmodulus hX hmodulusPos stride hs hstride index _ _
  have hperiodSp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp Psp) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = Real.exp ((m + 1 : ℕ) * Psp) := (Real.exp_nat_mul Psp (m + 1)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hmP hPsp])
  have hqM : residueRefinedPeriod modulus stride ≤ cutoff ^ (m + 1) :=
    allocatedRefinedPeriodIndex_power m hPsp index
  exact allocatedProductSeparatedContract_of_sampling B U b hR hσ S stride hs modulus tolerance
    (witnesses index) (hWitness index) hpAccuracy hAccuracySampling (allocatedSiteKernelMaskLog_nonneg m hPsp)
    (allocatedIdealProfileLog_nonneg m hpAccuracy he) he hE hPsp hdimSp hGsp hX hperiodSp hdimSmall
    hvars hI hn hJ cutoff hqM hcutoff hS le_rfl hEbudget le_rfl le_rfl o

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_allocated_early_product_source_family
    {Psp p e E : ℝ} (hPsp : 0 ≤ Psp) (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hmP : ((m + 1 : ℕ) : ℝ) ≤ Psp) (hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hGsp : (Fintype.card G : ℝ) ≤ Psp) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hEbudget : allocatedOriginalCoverAccuracy Psp (E + 1) + 4 ≤ p)
    (hα : Fintype.card (Fin dim) ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hcutoff : (allocatedRefinedPeriodCutoff m Psp : ℝ) ≤ Real.exp p)
    (hsize : (Fintype.card (Fin dim) + 1) * allocatedRefinedPeriodCutoff m Psp ≤ S.value)
    (hgamma : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      principalProfileSize (R (allocatedGridIntegerAxis B U b S a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B
          (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2)) ≤ 1)
    (hσ1 : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      σ (allocatedGridIntegerAxis B U b S a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp p)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 (allocatedRefinedPeriodCutoff m Psp) ≤ Real.exp p)
    (hB : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, max
      (positiveModerateSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val
        (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        ((layerTailDegree m + 2) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card))
      (uniformSpectrumBlockCount (allocatedGridIntegerAxis B U b S a).1.val
        (rowSets (allocatedGridIntegerAxis B U b S a).1).card
        (((allocatedGridIntegerAxis B U b S a).1.val + 1) * (rowSets (allocatedGridIntegerAxis B U b S a).1).card)) ≤
      Fintype.card (B ⟨(allocatedGridIntegerAxis B U b S a).1, Sum.inr (allocatedGridIntegerAxis B U b S a).2⟩)) :
    let w := allocatedSiteKernelMaskLog m Psp
    let v := allocatedIdealProfileLog m p e
    let accuracy := allocatedOriginalCoverAccuracy Psp (E + 1)
    let O := allocatedFullGridPrimitiveResourceLog m p w v accuracy
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m p)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) (allocatedSitePrimitiveTolerance m p w v accuracy)) ∧
      ∀ (pSampling : ℝ), p ≤ pSampling → (S.value : ℝ) ≤ Real.exp pSampling →
        AllocatedProductSeparatedUniformSourceContract.{uG,uI,uB,uJ,uQ,uX}
          B U b hR hσ S Psp E e p pSampling hPsp witnesses := by
  intro w v accuracy O
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hPsp
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hp he
  have haccuracy : 0 ≤ accuracy := by
    have hsp := coefficientErrorSpatialLog_nonneg hPsp
    dsimp only [accuracy, allocatedOriginalCoverAccuracy]
    linarith
  obtain ⟨witnesses, hBounds, hSampling⟩ := exists_allocated_early_full_grid_family
    B U b hR hσ S hPsp hp hw hv haccuracy hα hvars hI hn hcutoff hsize hgamma hσ1 L hL hcP hsP hB
  refine ⟨witnesses, hBounds, hSampling, ?_⟩
  intro pSampling hEarlyLate hS
  exact allocatedProductSeparatedUniformSourceContract_of_sampling
    B U b hR hσ S hPsp hE he hp hEarlyLate hmP hdimSp hGsp
    (by simpa only [Fintype.card_fin] using hα) hvars hI hn hJ hcutoff hS hEbudget witnesses hSampling

end Erdos3.VectorPolynomial

end

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
variable {p cEarly cLate P e Eraw E : ℝ}

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "accuracy" => allocatedOriginalCoverAccuracy P (E + 1)
local notation "pAccuracy" => allocatedCommonRefinedSourceLog m p cEarly P e 0 accuracy
local notation "pSampling" => allocatedCommonRefinedSourceLog m p cLate P e Eraw accuracy
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p cLate P e Eraw
local notation "maskLog" => allocatedSiteKernelMaskLog m P
local notation "profileLog" => allocatedIdealProfileLog m pAccuracy e
local notation "resourceLog" => allocatedFullGridPrimitiveResourceLog m pAccuracy maskLog profileLog accuracy
local notation "tolerance" => allocatedSitePrimitiveTolerance m pAccuracy maskLog profileLog accuracy

theorem exists_original_common_early_full_grid_source
    (hp : 0 ≤ p) (hcEarly : 0 ≤ cEarly) (hcLate : 0 ≤ cLate) (hEarlyLate : cEarly ≤ cLate)
    (hP : 0 ≤ P) (he : 0 ≤ e) (hEraw : 0 ≤ Eraw) (hE : 0 ≤ E)
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
      Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp resourceLog) (Real.exp resourceLog) (Real.exp resourceLog)
        ⟨Real.exp resourceLog, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      AllocatedProductSeparatedUniformSourceContract.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S P E e pAccuracy pSampling hP witnesses := by
  have hAccuracy : 0 ≤ accuracy := by
    have hsp := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  obtain ⟨hpAccuracy, hpBound, htwoP, _, _, hEbudget, hcutoffLog, hsourceLog, _, _, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hcEarly hP he (by norm_num : (0 : ℝ) ≤ 0) hAccuracy
  have hcutoff : (allocatedRefinedPeriodCutoff m P : ℝ) ≤ Real.exp pAccuracy :=
    (allocatedRefinedPeriodCutoff_bounds m hP).2.trans (Real.exp_le_exp.mpr hcutoffLog)
  have hcutoffNonneg : 0 ≤ allocatedRefinedPeriodLog m P + 1 := by
    unfold allocatedRefinedPeriodLog
    positivity
  have hEnvelope : canonicalScalarSourceEnvelope m (allocatedRefinedPeriodCutoff m P) ≤
      Real.exp pAccuracy :=
    (canonicalScalarSourceEnvelope_le_exp m hcutoffNonneg
      (allocatedRefinedPeriodCutoff_bounds m hP).2).trans (Real.exp_le_exp.mpr hsourceLog)
  obtain ⟨_, hcP, hsources⟩ := canonicalScalarSourceEnvelope_bounds m (allocatedRefinedPeriodCutoff m P)
  have hcutoffPower : allocatedRefinedPeriodCutoff m P ≤ allocatedRefinedPeriodCutoff m P ^ (m + 1) := by
    calc
      _ = allocatedRefinedPeriodCutoff m P ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (allocatedRefinedPeriodCutoff_bounds m hP).1 (by omega)
  have hsP : scalarCubePrimitiveEnvelope (Fin dim) scalarSourceTransitionBound 1 0
      (allocatedRefinedPeriodCutoff m P) ≤ Real.exp pAccuracy :=
    ((scalarCubePrimitiveEnvelope_mono (Fin dim) scalarSourceTransitionBound
      le_rfl le_rfl hcutoffPower).trans (hsources dim hdimSmall)).trans hEnvelope
  have hdimSp : ((dim + 1 : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (show dim + 1 ≤ m + 2 by omega)).trans hmP
  have hmOne : ((m + 1 : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (show m + 1 ≤ m + 2 by omega)).trans hmP
  have hGsp : (Fintype.card G : ℝ) ≤ P :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpP)
  obtain ⟨witnesses, hBounds, hSampling, hContracts⟩ := exists_allocated_early_product_source_family
    B U b hR hσ S hP hpAccuracy he hE hmOne hdimSp hGsp
    (fun j => (hJ j).trans htwoP) hEbudget
    (by simpa only [Fintype.card_fin] using hdimSmall)
    (hvars.trans hpBound) (fun j => (hI j).trans hpBound) (fun j => (hn j).trans hpBound)
    hcutoff (allocatedCommonScale_cutoff_window (G := G) B U b hR hσ hdimSmall hp hcLate hP he hEraw)
    (fun _ => (principalProfileSize_le_radius (hR _).le _).trans (hR1 _))
    (fun _ => hσ1 _) scalarSourceTransitionBound scalarSourceTransitionBound_spec.2
    (hcP.trans hEnvelope) hsP
    (fun a => hBlocks (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2)
  have hOrder : pAccuracy ≤ pSampling := allocatedCommonRefinedSourceLog_mono m
    hp hcEarly hP he (by norm_num : (0 : ℝ) ≤ 0) le_rfl hEarlyLate le_rfl le_rfl hEraw le_rfl
  have hS : ((LayerSamplerScale.value S) : ℝ) ≤ Real.exp pSampling :=
    original_common_period_scale_upper B U b hR hσ hp hcLate hP he hEraw hAccuracy
      hdimSmall hvars hI hn (fun j => (hRi j).trans (Real.exp_le_exp.mpr hEarlyLate)) hσi
  exact ⟨witnesses, hBounds, hSampling, hContracts pSampling hOrder hS⟩

end Erdos3.VectorPolynomial

end

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

local notation "Eraw" => (E + 1) + 4

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "accuracy" => allocatedOriginalCoverAccuracy P (E + 1)
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

theorem exists_original_common_early_raw_cover
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
    {A T Kproj Kideal Ksite : ℕ} (hKsite : 2 ≤ Ksite)
    (hSampling : AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim Ksite rowTypes rows)
    (hraw : AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B U b hR hσ D P (E + 1) e pNum δ A T Kproj Kideal) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp resourceLog) (Real.exp resourceLog) (Real.exp resourceLog)
        ⟨Real.exp resourceLog, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      AllocatedProductSeparatedRawData.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S P E e pNum Pbase
        (allocatedSourceSamplingBudget m dim A Pbase (E + 1) lateLog rawFourier)
        pAccuracy pSampling hP δ A (max T (max Kproj Kideal)) Ksite witnesses := by
  have hEraw : 0 ≤ Eraw := by linarith
  have hAccuracy : 0 ≤ accuracy := by
    have hsp := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  obtain ⟨hpAccuracy, _, _, hcAccuracy, _, _, _, _, _, _, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hcEarly hP he (by norm_num : (0 : ℝ) ≤ 0) hAccuracy
  obtain ⟨witnesses, hBounds, hWitnesses, hContracts⟩ :=
    exists_original_common_early_full_grid_source.{uG,uI,uB,uJ,uQ,uX}
      B U b hR hσ hp hcEarly hcLate hEarlyLate hP he hEraw hE
      hdimSmall hmP hpP hvars hI hn hJ hR1 hσ1 hRi hσi hBlocks
  refine ⟨witnesses, hBounds, hWitnesses, ?_⟩
  have hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp P :=
    (hvars.trans hpP).trans (by linarith [Real.add_one_le_exp P])
  exact allocatedProductSeparatedRawData_of_source.{uG,uI,uB,uJ,uQ,uX}
    B U b hR hσ S hP hE he hpAccuracy hvarsGrowth
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hcAccuracy))
    hδ hδ1 hδe hKsite hSampling (allocatedRawSourceData_of_original B U b hR hσ hraw)
    witnesses hContracts

end Erdos3.VectorPolynomial

end

end OAI
