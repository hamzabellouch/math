import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthHighBound

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthSource
open HeckeFamily QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroGrowthHighBound
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction CenteredMomentEnergyBandMonotonicity
open CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

def PhysicalGrowthAt (Q:Ideal O)(a b bΦ Bmask L rho Mcap ξ e Z:ℝ)(ha:0<a)
    (Ψ:𝓢(ℝ,ℂ))(S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→ rho≤s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→5*s.width/6≤length Z X₁+length Z X₂→
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
    (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
      Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
    physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
      C*(p.control S)^2*(1+|t|)^J*Z^(max s.width (length Z X₁+length Z X₂)+e)

theorem actual_growth_from_physical
    (a b bΦ rho ε Mcap Bmask B L εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hLB:2*L≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass:ℝ),
      0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroAt Q a b bΦ Bmask L rho efinal Z Jout U (Cfixed*(K+Cmass+1))→
      ZeroLowAt Q a b bΦ Bmask (max L (Mcap+Bmask+rho/100)) Mcap e Z degree S K→
      PhysicalGrowthAt Q a b bΦ Bmask L rho Mcap ξ emass Z ha Ψ Smass Jmass Cmass→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap efinal Z Jout U (Cfixed*(K+Cmass+1)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,hstage⟩:=actual_high_from_physical a b bΦ rho ε Mcap Bmask B εdiag ξ saving
    ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Jh,Uh,Ch,hCh,hbound⟩:=hstage degree S Jmass Smass
  let Jout:=degree+Jh
  let U:=S∪Uh
  let Cfixed:=Ch+1
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];linarith
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hold hlow hmass
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hCout:0≤Cfixed*(K+Cmass+1):=by positivity
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  by_cases hsmall:s.width≤ rho
  · exact zeroGrowth_of_zeroAt Q a b bΦ Bmask L rho efinal Z Jout U
      (Cfixed*(K+Cmass+1)) hCout hold s hQ hsmall p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hbase:1≤1+|t|:=by linarith [abs_nonneg t]
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hS:S⊆U:=Finset.subset_union_left
  have hUh:Uh⊆U:=Finset.subset_union_right
  have hlowL:=low_restrict Q a b bΦ Bmask _ L Mcap e Z degree S K hZ.1.le (le_max_left _ _) hlow
  by_cases hl:length Z X₁+length Z X₂≤5*s.width/6
  · have hh:=hlowL s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ hbase hj
    have hloss:s.width+e≤max s.width (length Z X₁+length Z X₂)+efinal:=by
      linarith [le_max_left s.width (length Z X₁+length Z X₂)]
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hloss
    have hcoeff:K≤Cfixed*(K+Cmass+1):=by dsimp [Cfixed];nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm]
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
  have hlowR:=low_restrict Q a b bΦ Bmask _ (Mcap+Bmask+rho/100) Mcap e Z degree S K
    hZ.1.le (le_max_right _ _) hlow
  have hvolume:X₁*X₂≤Z^B:=by
    calc
      _≤Z^L*Z^L:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLB
  have hp:=hmass s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (le_of_not_ge hl)
  have hh:=hZ.2 e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hlowR
    s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hvolume (le_of_not_ge hl) hp
  have hcontrol:=profile_control_mono p hUh
  have hp0:=p.control_nonneg Uh
  have hj:Jh≤Jout:=Nat.le_add_left _ _
  have hpow:=pow_le_pow_right₀ hbase hj
  have hcoeff:Ch≤Cfixed:=by dsimp [Cfixed];linarith
  apply hh.trans
  rw [Real.norm_eq_abs]
  gcongr

end SevenEighths.CenteredMomentEnergyZeroGrowthSource

end

end OAI
