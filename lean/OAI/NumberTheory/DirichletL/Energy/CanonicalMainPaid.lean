import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainPaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

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

omit [DecidableEq α] in
lemma common_raw_caps (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (τ:Character)(t F:ℝ)(h₁:src.X₁≤F)(h₂:src.X₂≤F)(h₃:src.Y₁≤F)(h₄:src.Y₂≤F):
    let d:=commonData (withHeight src τ t) C R B
    d.X₁≤F ∧ d.X₂≤F ∧ d.Y₁≤F ∧ d.Y₂≤F:=by
  have hN (j:α⊕Fin 2):(1:ℝ)≤Ideal.absNorm (B.val j):=
    norm_ge_one _ (alloc_ne src C B j)
  exact ⟨(div_le_self src.X₁_pos.le (hN _)).trans h₁,
    (div_le_self src.X₂_pos.le (hN _)).trans h₂,
    (div_le_self src.Y₁_pos.le (hN _)).trans h₃,
    (div_le_self src.Y₂_pos.le (hN _)).trans h₄⟩

theorem actual_main_child_from_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
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
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock τ t Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kmain dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family τ C₂ D₂ hC₂ hD₂ U family →
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
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(sigma/3+δpaid/6+θclip/3)+κ*mesh):=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=original_subsets_reference_paid (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀
  refine ⟨Z₀,hZ₀,?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource hK hsigma hcost hasource
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hz:1<Z:=hZ₀.trans_le hZ
  have hcost0:0<cost:=zero_lt_one.trans_le hcost
  let input:=child src C R0 B τ t
  let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
  have hKmain:0<Kmain:=by dsimp [Kmain];unfold mainCommonRadius;positivity
  have hP:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hz.le (hw i)
  have hcap':length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤Mdecl:=by
    simpa only [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hcap
  obtain ⟨hδ,hpar,hshift⟩:=actual_main_admission src τ τ C D R0 hC hD hCD E B t hB
    K Z sigma delta reserve cost asource hK hz hcost0 hasource hmod Scols βsource C₂ D₂
    hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical Cpick Rpick hside B₂ hB₂
    κ Mdecl hκsmall hP hcap' hMdecl
  have hm:=matches_child M H hH hmatch C R0 B τ t
  have caps₁:=common_raw_caps src C R0 B τ t (Z^L) hX₁ hX₂ hY₁ hY₂
  have caps₂:=common_raw_caps input Cpick Rpick B₂ (family χ) v (Z^L)
    caps₁.1 caps₁.2.1 caps₁.2.2.1 caps₁.2.2.2
  have hτnorm:0<(τ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hq:(τ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ):=by nlinarith
  have hdef:=actual_width_le_reference hfamily t Scols βsource Rwindow rows Wkernel Kmain hKmain dyad
    hphysical (cost*(τ.modulus.absNorm:ℝ)) Z hq hz χ
  have hn:=actual_dyad_ge_one t Scols βsource Rwindow rows Wkernel Kmain dyad hphysical
  have hh:=hbound (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>θ i.val)
    Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) v height mesh hmesh
    (fun i=>hw i.val) (fun i=>hwm i.val) (fun i=>hwL i.val) (fun i=>hσlo i.val)
    (fun i=>hσhi i.val) hheight (fun i=>hfreq i.val) input hm
    (fun i=>hhi i.val) (fun i=>hMs i.val) Cpick Rpick B₂ Dalloc alloc hRpick
    (family χ) dyad hn hwidth p hp₁ hp₂ caps₂.1 caps₂.2.1 caps₂.2.2.1 caps₂.2.2.2
    (Real.logb Z (volume src)) Mdecl (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad)
    0 (sigma/3) _ 0 θclip (envelope_pos _ (mul_pos hcost0 hτnorm) _ _ hC₂ _ _) le_rfl
    (by positivity) hδ le_rfl hθclip
    (by simpa only [input,CenteredMomentAmplificationChildInput.child,commonData,withHeight,hmatch.scale,
      Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hpar)
    (by simpa only [CenteredMomentAllocatedChildCapacity.preVolume,commonData,withHeight,
      zero_add] using hshift)
    (by linarith) hclip
  simpa only [zero_add] using hh

end SevenEighths.CenteredMomentEnergyCanonicalMainPaid

end

end OAI
