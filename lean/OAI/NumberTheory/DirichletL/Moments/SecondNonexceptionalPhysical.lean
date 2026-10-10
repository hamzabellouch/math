import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondNonexceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

lemma paired_sqrt (A E₁ E₂ c d:ℝ) (hA:0≤A) (hE₁:0≤E₁) (hE₂:0≤E₂)
    (hc:0<c) (_hd:0<d) :
    Real.sqrt (A*E₁/c)*Real.sqrt (A*E₂/d)=A/Real.sqrt (c*d)*Real.sqrt (E₁*E₂) := by
  rw [←Real.sqrt_mul (div_nonneg (mul_nonneg hA hE₁) hc.le)]
  rw [show A*E₁/c*(A*E₂/d)=A^2*(E₁*E₂)/(c*d) by ring]
  rw [Real.sqrt_div (mul_nonneg (sq_nonneg A) (mul_nonneg hE₁ hE₂)),
    Real.sqrt_mul (sq_nonneg A),Real.sqrt_sq hA]
  ring

omit [DecidableEq ι] in
theorem paired_core_budget (s:Input ι) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (Ce Z δ E₁ E₂ t:ℝ) (hCe:0≤Ce) (hZ:0≤Z) (hE₁:0≤E₁) (hE₂:0≤E₂)
    (J₁ J₂:ℕ) :
    windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)=
      (Ce*Z^δ*profileCost s*volume s.toData)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hA:0≤Ce*Z^δ*profileCost s*volume s.toData:=by
    exact mul_nonneg (mul_nonneg (mul_nonneg hCe (Real.rpow_nonneg hZ _)) (profileCost_nonneg s)) (volume_pos s.toData).le
  have he (G:Ideal O) (E:ℝ):core s G Ce Z δ E=
      (Ce*Z^δ*profileCost s*volume s.toData)*E/(G.absNorm:ℝ):=by
    unfold core volume
    ring
  rw [he C E₁,he D E₂]
  simp only [windowBudget,pow_add]
  have hh:=paired_sqrt _ E₁ E₂ _ _ hA hE₁ hE₂ hc hd
  calc
    _=(Real.sqrt (_*E₁/(C.absNorm:ℝ))*Real.sqrt (_*E₂/(D.absNorm:ℝ)))*
      (heightEnvelope t^J₁*heightEnvelope t^J₂)*profileMoment J₁*profileMoment J₂:=by ring
    _=_:=by rw [hh]

theorem actual_physical_from_supported_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (s:Input ι),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^B →
      ∀(R:ℝ) (rows:Finset O),
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0<H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^decay := by
  obtain ⟨C0,Ce,hC0,hCe,hkernel⟩:=actual_block_from_supported_children lo hi W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n r η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ Hsource hβ hn
    R rows Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hr:0<r:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hpow:0<(1+r)^decay:=pow_pos (by linarith) _
  have hh:=hZ.2 r hr η τ t s hlo hhi R0 seed C D hC hD hsC hsD hnC hnD hCD U hτ Hsource hβ hn
    R rows (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
    Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  change (1+r)^decay*‖normalizedBlock η t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  rw [paired_core_budget s C D hC hD Ce Z δ E₁ E₂ t hCe.le
    (zero_lt_one.trans hZ.1).le hE₁ hE₂ J₁ J₂] at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar;positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  have hnrows:∀z∈rows,z≠0:=fun z hz=>(hrows z hz).1
  have hp:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)
  have hphys:‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖=
      outerScalar C D Kphys n*normalizer C D U*
        ‖normalizedBlock η t S β C D hC hD U R rows W Kphys n‖:=by
    rw [physicalBlock_eq η t S β C D hC hD U R rows hnrows W Kphys hKphys n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  rw [hphys]
  apply (div_le_iff₀ (volume_pos s.toData)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpow).mpr
  have hzz:Z^(2*δ)=Z^δ*Z^δ:=by
    rw [show 2*δ=δ+δ by ring,Real.rpow_add (zero_lt_one.trans hZ.1)]
  rw [hzz]
  convert hp using 1 <;> ring

end SevenEighths.CenteredMomentSecondNonexceptionalPhysical

end

end OAI
