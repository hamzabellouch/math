import OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid
import OAI.NumberTheory.DirichletL.Energy.CanonicalNestedReference
import OAI.NumberTheory.DirichletL.Energy.ActiveChildRestoration
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][instα:DecidableEq α]

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

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentEnergyActiveChildRestoration

def castAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C):actualAllocations t.pools C:=
  ⟨B.val,by rw [←h];exact B.property⟩

def castDivisorAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val⊕Fin 2)):=alloc

def restoreDivisorAllocation (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val⊕Fin 2)):=alloc

lemma cast_child_energy (s t:Input α)(h:s=t)(C R:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(v:ℝ)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    childEnergy (commonData (withHeight s τ v) C R B) rad D alloc=
      childEnergy (commonData (withHeight t τ v) C R (castAllocation s t h C B)) rad D
        (castDivisorAllocation s t h C B D alloc):=by
  subst t
  rfl

lemma restored_child_energy (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    childEnergy (commonData (withHeight (activeInput s) τ v) C R B) rad D alloc=
      childEnergy (commonData (withHeight s τ v) C R (restoreAllocation s C B)) rad D
        (restoreDivisorAllocation s C B D alloc):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  exact child_energy_active s C R B τ v D alloc rad

omit instα in
lemma cast_preVolume (s t:Input α)(h:s=t)(C R:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(v:ℝ):
    CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight t τ v) C R (castAllocation s t h C B))=
      CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight s τ v) C R B):=by
  subst t
  rfl

omit instα in
lemma cast_slot_sum (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(f:α→ℝ):
    (∑i:CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val,f i.val)=
      ∑i:CenteredMomentCommonProfile.liveIndices B.val,f i.val:=rfl

omit instα in
lemma restored_preVolume (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ):
    CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight s τ v) C R (restoreAllocation s C B))=
      CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight (activeInput s) τ v) C R B):=rfl

omit instα in
lemma restored_slot_sum (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(f:α→ℝ):
    (∑i:CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val,f i.val)=
      ∑i:CenteredMomentCommonProfile.liveIndices B.val,f i.val:=rfl

theorem actual_error_child_from_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    let δpaid:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      Cc*(Ideal.absNorm (Rpick*Cpick).radical:ℝ)^εmask*(C₀+C₁)*
        diagonalControl (canonicalRadial (family χ) (internalQ Q η₀) dyad).profile*
        (p.control T)^2*(1+(|v|+height))^(dc+degree+4*n)*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(errorRemoval prime Z k+δpaid/6+θclip/3)+κ*mesh):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=nested_original_subsets_reference_paid (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀
  refine ⟨Z₀,hZ₀,?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource hK hsigma hcost hasource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  subst input
  have hz:1<Z:=hZ₀.trans_le hZ
  have hcost0:0<cost:=zero_lt_one.trans_le hcost
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let restored:=restoredError src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have heInput:input=activeInput restored:=by
    exact error_source_active src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let B₂a:=castAllocation input (activeInput restored) heInput Cpick B₂
  let B₂r:=restoreAllocation restored Cpick B₂a
  let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
  have hKerror:0<Kerror:=by dsimp [Kerror];unfold errorCommonRadius;positivity
  have hP:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hz.le (hw i)
  have hcap':length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤Mdecl:=by
    simpa only [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hcap
  obtain ⟨hδ,hpar,hshift⟩:=actual_active_error_admission src τ υ C D R0 hC hD hCD E B t hB
    K Z sigma delta reserve cost asource hK hz hcost0 hasource prime hprime k hk hsigma hprimeScale
    hslot Bp v0 hmod Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    Cpick Rpick hside B₂ hB₂ κ Mdecl hκsmall hP hcap' hMdecl
  have hm:=restoredError_matches M H hH hmatch C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have caps₁:=common_raw_caps src C R0 B τ t (Z^L) hX₁ hX₂ hY₁ hY₂
  have caps₂:=common_raw_caps (child src C R0 B τ t) ((Ideal.span {prime})^k) (R0*C)
    (restoreAllocation (child src C R0 B τ t) ((Ideal.span {prime})^k) Bp) υ v0 (Z^L)
    caps₁.1 caps₁.2.1 caps₁.2.2.1 caps₁.2.2.2
  have caps₃:=common_raw_caps restored Cpick Rpick B₂r (family χ) v (Z^L)
    caps₂.1 caps₂.2.1 caps₂.2.2.1 caps₂.2.2.2
  have hτnorm:0<(τ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hqpos:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=by positivity
  have hdef:=actual_width_le_reference hfamily v0 Scols βsource Rwindow rows Wkernel Kerror hKerror dyad
    hphysical (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) Z hυ hz χ
  have hn:=actual_dyad_ge_one v0 Scols βsource Rwindow rows Wkernel Kerror dyad hphysical
  have hrem:0≤errorRemoval prime Z k:=by
    have hn:0≤Real.logb Z (normValue prime):=by linarith
    unfold errorRemoval
    positivity
  have hsum:(∑i:CenteredMomentCommonProfile.liveIndices B₂.val,Real.logb Z (input.P i.val))=
      ∑i:CenteredMomentCommonProfile.liveIndices B₂.val,w i.val.val.val:=by
    apply Finset.sum_congr rfl
    intro i hi
    change Real.logb Z (src.P i.val.val.val)=w i.val.val.val
    rw [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne']
  have hparw:Real.logb Z (volume src)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B₂r.val,w i.val.val.val)≤Mdecl:=by
    rw [hsum] at hpar
    have heSum := (restored_slot_sum restored Cpick B₂a (fun i=>w i.val.val)).trans
      (cast_slot_sum input (activeInput restored) heInput Cpick B₂ (fun i=>w i.val.val))
    exact (congrArg (fun x=>Real.logb Z (volume src)+(6*κ-1)*x) heSum).trans_le hpar
  have hshiftw:
      Real.logb Z ((commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₁*
        (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₂*
        ∏i:CenteredMomentCommonProfile.liveIndices B₂r.val,restored.P i.val)-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)≤
      Real.logb Z (volume src)-Mdecl+6*(errorRemoval prime Z k+0)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          sourceReserve src input C D Z delta reserve cost asource)+Real.logb Z (ratioPenalty dyad):=by
    change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume
      (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r))-_≤_
    have hpv:= (restored_preVolume restored Cpick Rpick B₂a (family χ) v).trans
      ((cast_preVolume input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v).trans
        (common_preVolume_height input Cpick Rpick B₂ (family χ) υ v v0))
    calc
      _ = Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume
          (commonData (withHeight input υ v0) Cpick Rpick B₂)) -
          Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad) :=
        congrArg (fun x=>Real.logb Z x - Real.logb Z
          (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)) hpv
      _ ≤ _ := by
        dsimp only [input]
        simpa only [add_zero] using hshift
  have hh:=hbound (CenteredMomentCommonProfile.liveIndices B.val)
    (CenteredMomentCommonProfile.liveIndices Bp.val) (fun i=>θ i.val.val)
    Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    (fun i=>w i.val.val) (fun i=>σ i.val.val) (fun i=>freq i.val.val) v height mesh hmesh
    (fun i=>hw i.val.val) (fun i=>hwm i.val.val) (fun i=>hwL i.val.val) (fun i=>hσlo i.val.val)
    (fun i=>hσhi i.val.val) hheight (fun i=>hfreq i.val.val)
  have hh := hh restored hm (fun i=>hhi i.val.val) (fun i=>hMs i.val.val)
  have hh := hh Cpick Rpick B₂r
  let allocA:=castDivisorAllocation input (activeInput restored) heInput Cpick B₂ Dalloc alloc
  let allocR:=restoreDivisorAllocation restored Cpick B₂a Dalloc allocA
  have hh := hh Dalloc allocR hRpick
  have hh := hh (family χ) dyad hn hwidth
  have hh := hh p hp₁ hp₂
  have hh := hh caps₃.1 caps₃.2.1 caps₃.2.2.1 caps₃.2.2.2
  have hh := hh (Real.logb Z (volume src)) Mdecl
    (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)
    (errorRemoval prime Z k) 0
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource)
    0 θclip (envelope_pos _ hqpos _ _ hC₂ _ _)
    hrem le_rfl hδ le_rfl hθclip
  have hh := hh hparw
  have hh := hh hshiftw
  have hh := hh (by linarith only [hdef]) hclip
  have he := (cast_child_energy input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v Dalloc alloc
    (canonicalRadial (family χ) (internalQ Q η₀) dyad)).trans
      (restored_child_energy restored Cpick Rpick B₂a (family χ) v Dalloc allocA
        (canonicalRadial (family χ) (internalQ Q η₀) dyad))
  apply he.trans_le
  simpa only [zero_add,add_zero] using hh

end SevenEighths.CenteredMomentEnergyCanonicalErrorPaid

end

end OAI
