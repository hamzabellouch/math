import OAI.NumberTheory.DirichletL.Moments.FirstSourceReduction
import OAI.NumberTheory.DirichletL.Moments.SecondActivePhysicalDictionary

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalActiveDictionary
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive IdealMobiusDivisorSum
open CenteredMomentFirstPhysicalSource CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

theorem columns_active (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) :
    columns C D hD (activeSource S β)=
      (columns C D hD S).filter (fun I=>β (D*I)≠0) := by
  ext I
  simp only [columns,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

theorem element_value (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (I : columns C D hD S) :
    element C D hD S I=CompletedGauss.primaryGenerator (I:Ideal O) := rfl

theorem column_sum_active (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (β f : Ideal O→ℂ) (hf : ∀I,β (D*I)=0→f I=0) :
    (∑I∈columns C D hD (activeSource S β),f I)=∑I∈columns C D hD S,f I := by
  rw [columns_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β (D*I)=0
  · simp only [hi,ne_eq,not_true_eq_false,ite_false,hf I hi]
  · simp only [hi,ne_eq,not_false_eq_true,ite_true]

theorem column_pair_sum_active (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (f : Ideal O→Ideal O→ℂ)
    (hl : ∀I J,β (C*I)=0→f I J=0) (hr : ∀I J,β (D*J)=0→f I J=0) :
    (∑I∈columns C C hC (activeSource S β),∑J∈columns C D hD (activeSource S β),f I J)=
      ∑I∈columns C C hC S,∑J∈columns C D hD S,f I J := by
  simp_rw [column_sum_active C D hD S β _ (fun J h=>hr _ J h)]
  apply column_sum_active C C hC S β
  intro I hi
  exact Finset.sum_eq_zero (fun J hJ=>hl I J hi)

lemma primary_supported (I : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {CompletedGauss.primaryGenerator I}) := by
  rw [primary_span_supported I hI]
  exact hI

def physicalTerm (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    let na:=CompletedGauss.primaryGenerator I
    let nb:=CompletedGauss.primaryGenerator J
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    if IsCoprime I J then
      (tripleRow na nb r (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) e *
      ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
      tripleFourier na nb r
        (supported_element_ne_zero _ (primary_supported I hI))
        (supported_element_ne_zero _ (primary_supported J hJ))
        (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) h)*
      (coefficient η m A t β C I*star (coefficient η m A t β D J))*
      windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
        (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
      EisensteinSchwartzPoisson.paperRadialFourier W
        (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
    else 0
  else 0 else 0

theorem physicalTerm_zero_left (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hi : β (C*I)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,coefficient,hi,zero_mul,mul_zero]
  split_ifs <;> rfl

theorem physicalTerm_zero_right (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hj : β (D*J)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,coefficient,hj,zero_mul,star_zero,mul_zero]
  split_ifs <;> rfl

theorem block_eq_ideal_sums (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      inactiveWeight C D E * ∑h∈rows,
        ∑I∈columns C C hC.1 S,∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
  unfold block
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=∑I:columns C C hC.1 S,∑J:columns C D hD.1 S,
        physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [physicalTerm,dite_eq_left (column_supported C C hC.1 S I),
        dite_eq_left (column_supported C D hD.1 S J),element]
      rfl
    _=_ := by
      simp_rw [Finset.sum_coe_sort]
      exact Finset.sum_coe_sort (columns C C hC.1 S)
        (fun I=>∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J)

theorem block_active (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  rw [block_eq_ideal_sums,block_eq_ideal_sums]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  exact column_pair_sum_active C D hC.1 hD.1 S β
    (physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h)
    (fun I J hi=>physicalTerm_zero_left η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hi)
    (fun I J hj=>physicalTerm_zero_right η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hj)

theorem block_active_ne_zero_iff (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 ↔
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 := by
  rw [block_active]

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
open CenteredMomentCommonRadialData CenteredMomentFirstRetainedNorm
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentLogDyadic

theorem original_dyadic_block_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
    block s.η m A t (activeSource S β) β C D hC hD E rows W
      (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))=
    block s.η m A t S β C D hC hD E rows W
      (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  apply block_active

theorem original_sector_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sector s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sector s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sector
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  apply block_active

theorem original_sectorMass_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sectorMass s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_active]

theorem original_retained_full_sectorMass [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0<K) :
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ := by
  dsimp only
  apply (original_retained_norm s R seed hz₁ hz₂ m A t S W K X Z ξ hK).trans_eq
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ W K X Z ξ

theorem active_sectorMass_sum (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    let T:=activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ)=
    ∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t S p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ := by
  dsimp only
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ Φ K X Z ξ

theorem physicalMass_full_source [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ := by
  exact active_sectorMass_sum s R seed m A s.t
    (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)) Φ K
    (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ

theorem normalized_physicalMass_full_source [DecidableEq ι] (s : Input ι)
    (R seed : Ideal O) (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ /
        CenteredMomentExceptionalAmplitudePair.volume s.toData=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      (∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ) /
        CenteredMomentExceptionalAmplitudePair.volume s.toData := by
  exact congrArg (fun x:ℝ=>x/CenteredMomentExceptionalAmplitudePair.volume s.toData)
    (physicalMass_full_source s R seed m A Φ K Z ξ)

end SevenEighths.CenteredMomentFirstPhysicalActiveDictionary

end

end OAI
