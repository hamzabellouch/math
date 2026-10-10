import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

def weight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r:ℝ)(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂:Character)
    (n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)):ℝ:=
  let h:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  if block s.η m A t (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) p.val.1 p.val.2 h.1 h.2 E
      (CenteredMomentSecondRetainedRows.retainedRows r 1) W V K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0 then 0
  else ‖scalar p.val.1 p.val.2 h.1 E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*
    volume s.toData/((p.val.1.absNorm:ℝ)*p.val.2.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)

theorem weight_le (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r a₁ a₂ M F:ℝ)(hK:0<K)(ha₁:0<a₁)(ha₂:0<a₂)(hF:0≤F)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hwin:∀i y,V i y≠0→|y|≤M)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(τ₁ τ₂:Character)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)
    (n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)):
    weight s R seed m A t W V K r p E τ₁ τ₂ n≤
      ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ))*
        (CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
          (commonRadical p.val.1 p.val.2).absNorm):=by
  have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  unfold weight
  dsimp only
  split_ifs with hn
  · exact mul_nonneg (by positivity)
      (div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _)
        (Nat.cast_nonneg _))
  · have hh:=original_scalar_conductors s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ m A t _
      p.val.1 p.val.2 hp.1 hp.2 E _ W V K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) M F τ₁ τ₂ hK
      (dyadicScale_pos _) (dyadicScale_pos _) hF hwin hn hc₁ hc₂
    convert hh using 1 ;
      simp only [CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,
        div_one,CenteredMomentFirstPhysicalSource.inactiveWeight] ; ring

def sectorWeight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r:ℝ)(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂:Character):ℝ:=
  ∑n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),
    weight s R seed m A t W V K r p E τ₁ τ₂ n

def sumWeight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K:ℝ)(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
    (τ₁ τ₂:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→Character):ℝ:=
  ∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
    sectorWeight s R seed m A t W V K (radius p E) p E (τ₁ p E) (τ₂ p E)

theorem original_weight_sum (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0<sourceRadius s→sourceRadius s≤Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M F:ℝ),
      0<K→0<a₁→0<a₂→0≤F→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
      (τ₁ τ₂:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→Character),
      (∀p E,radius p E≤Cr*Z^L)→
      (∀p E,((τ₁ p E).modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
        ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
        ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)→
      (∀p E,((τ₂ p E).modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
        ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
        ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)→
      sumWeight s R seed m A t W V K radius τ₁ τ₂≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨Cd,hCd,hd⟩:=original_blocks_subpower B L Cr (ε/2) hB hL hCr (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=CenteredMomentFirstInactiveRadicalMass.actual_inactive_radical_mass
    B (ε/2) hB (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ)] with Z hd hZ
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M F
    hK ha₁ ha₂ hF hs₁ hs₂ hwin radius τ₁ τ₂ hr hc₁ hc₂
  let P:ℝ:=(Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ)
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  have hP:0≤P:=by dsimp [P];positivity
  let f:=fun (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))=>
    CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
      (commonRadical p.val.1 p.val.2).absNorm
  have hf:∀p E,0≤f p E:=by
    intro p E
    exact div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)
  have hb (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
      sectorWeight s R seed m A t W V K (radius p E) p E (τ₁ p E) (τ₂ p E)≤
        (Cd*Z^(ε/2)*P)*f p E:=by
    unfold sectorWeight
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard:=hd p.val.1 p.val.2 hp.1.1 hp.2.1 E K (radius p E) (sourceRadius s)
      hK hH (hr p E) hHcap
    calc
      _≤∑_n:Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),P*f p E:=by
        apply Finset.sum_le_sum
        intro n hn
        exact weight_le s R seed m A t W V K (radius p E) a₁ a₂ M F hK ha₁ ha₂ hF
          hs₁ hs₂ hwin p E (τ₁ p E) (τ₂ p E) (hc₁ p E) (hc₂ p E) n
      _≤_:=by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        convert mul_le_mul_of_nonneg_right hcard (mul_nonneg hP (hf p E)) using 1 ; ring
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI=>original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hHcap) 0 le_rfl
  calc
    _≤∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*P)*f p E:=by
      unfold sumWeight
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro E hE
      exact hb p E
    _=(Cd*Z^(ε/2)*P)*
        (∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,f p E):=by
      simp only [Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*P)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=P*((Cd*Cm)*Z^ε/(seed.absNorm:ℝ)):=by
      have hz:0<Z:=by linarith
      have he:Z^(ε/2)*Z^(ε/2)=Z^ε:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=P*(Cd*Cm)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ):=by ring
        _=_:=by rw [he];ring

end SevenEighths.CenteredMomentFirstNonexceptionalWeightSum

end

end OAI
