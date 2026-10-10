import OAI.NumberTheory.DirichletL.Energy.FirstRightAdmission
import OAI.NumberTheory.DirichletL.Energy.CanonicalHighColumn
import OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport
import OAI.NumberTheory.DirichletL.Energy.CanonicalLowColumn
import OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularPower
import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedColumn
import OAI.NumberTheory.DirichletL.Energy.FirstLowHomogeneousPowers
import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedUniform
import OAI.NumberTheory.DirichletL.Energy.AmplifierFamilyAdmission
import OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission
import OAI.NumberTheory.DirichletL.Energy.FirstRawScaleAdmission
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSubsets
import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorSubsets
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainHomogeneous
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparatedPower
import OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparated
import OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients
import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
import OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainUniform
import OAI.NumberTheory.DirichletL.Moments.FirstSeededGaussianPower
import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid
import OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidReserve
import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPower CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower CenteredMomentEnergyFirstLowHomogeneousPowers
open CenteredMomentEnergyCanonicalLowColumn CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentEnergyFirstRightAdmission

theorem actual_original_right_low_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(D.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance D C Z);
    (commonEnergy (original src R0 seed0) D hD τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=actual_admitted_subsets_low_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_right_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=eventually_right_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hlow t
  subst τ
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedD:seed0∣D:=hcols.2.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hND:(D.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.2.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  let Es:=swapSubset C D E
  have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
    exact right_modulus src.η C D hC E χ₁ χ₂ F
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies F.right
  have hnom:firstNominalScale D C
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es}) K (volume src)=
      firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src):=by
    dsimp only [Es]
    rw [swapSubset_generator,nominal_swap]
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale D C (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es})
        K (volume src)) Z ξ:=by
    rw [hnom]
    simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max D C R0 hD hC hCD.symm hR0 hRcap hND Es hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedD
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hlow
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock B t seed hB
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hm.2.1
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    let input:=child src D R0 B F.right t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hz:∀j,z j≤eta:=fun j=>hweta j.val
    have hlen:∀j,input.P j=Z^(z j):=fun j=>hmatch.scale j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hslot:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact original_slot_coprime (original input (R0*D) seed).active Z sigma (max 1 bslot) eta
        hZ.le (by positivity) hseparate z hz hlen hsupp
        (original input (R0*D) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*D) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun j=>n j) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock B t seed hB M H fixedBadPrimes (Finset.Subset.refl _) prime.val prime.property
      (errorIndex i+1) hk' hslot Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hN)
    rcases he.2 with hdead|hlive
    · exact Or.inl hdead.1
    · exact Or.inr (by simpa only [mul_one] using hlive.1)

theorem actual_original_right_high_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤src.X₁ → Z^(Mwidth/4)≤src.X₂ →
    Z^(Mwidth/4)≤src.Y₁ → Z^(Mwidth/4)≤src.Y₂ →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(D.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance D C Z);
    (commonEnergy (original src R0 seed0) D hD τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=CenteredMomentEnergyCanonicalHighColumn.actual_admitted_subsets_high_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_right_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=eventually_right_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ t
  subst τ
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedD:seed0∣D:=hcols.2.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hND:(D.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.2.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  let Es:=swapSubset C D E
  have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
    exact right_modulus src.η C D hC E χ₁ χ₂ F
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies F.right
  have hnom:firstNominalScale D C
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es}) K (volume src)=
      firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src):=by
    dsimp only [Es]
    rw [swapSubset_generator,nominal_swap]
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale D C (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es})
        K (volume src)) Z ξ:=by
    rw [hnom]
    simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max D C R0 hD hC hCD.symm hR0 hRcap hND Es hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedD
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock B t seed hB
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hm.2.1
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    let input:=child src D R0 B F.right t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hz:∀j,z j≤eta:=fun j=>hweta j.val
    have hlen:∀j,input.P j=Z^(z j):=fun j=>hmatch.scale j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hslot:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact original_slot_coprime (original input (R0*D) seed).active Z sigma (max 1 bslot) eta
        hZ.le (by positivity) hseparate z hz hlen hsupp
        (original input (R0*D) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*D) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun j=>n j) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock B t seed hB M H fixedBadPrimes (Finset.Subset.refl _) prime.val prime.property
      (errorIndex i+1) hk' hslot Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hN)
    rcases he.2 with hdead|hlive
    · exact Or.inl hdead.1
    · exact Or.inr (by simpa only [mul_one] using hlive.1)

end SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn

end

end OAI
