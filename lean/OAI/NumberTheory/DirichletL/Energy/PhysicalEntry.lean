import OAI.NumberTheory.DirichletL.Energy.OriginalSource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPhysicalEntry
open HeckeFamily CenteredMomentEnergyOriginalSource CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentExceptionalAmplitudePair
open CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance physicalEntryDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem positive_first_physical_entry (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(R:Ideal O)(r:CenteredMomentRadialEligibleEnergy.Radial),
      volume s.toData≤Z^B→(r.scale)⁻¹≤Z^B→
      energy s.η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*physicalMass s R 1 fixedBadMask 1 r.profile r.scale Z ξ/volume s.toData+
      2*Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*r.scale*Z^ε+
      2*Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*r.scale*Z^(-saving)+
      2*energy s.η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale:=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,h⟩:=
    original_first_physical_reduction hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R r hV hK
  have hh:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi fixedBadMask 1
    (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 r.profile r.scale r.scale_pos hV hK
  have hc:=positive_energy_comparison s R r
  change _≤2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale‖/
      volume s.toData+_ at hc
  rw [mul_div_assoc] at hc ⊢
  linarith

lemma natural_inverse_scale {Z Bmask bΦ:ℝ} (state:NaturalState Z Bmask bΦ)
    (B:ℝ)(hB:0≤B):state.radial.scale⁻¹≤Z^B:=by
  have hscale:1≤state.radial.scale:=by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  exact (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow state.base_ge_one hB)

theorem natural_first_physical_entry (a b bslot B ε ξ saving Bmask bΦ:ℝ)
    (ha:0<a)(hb:0≤b)(hbslot:0≤bslot)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(state:NaturalState Z Bmask bΦ)(p:Profiles a b),
    ∀(slots:ι→Finset (Ideal O))(hp:∀i,∀I∈slots i,Prime I)
      (ν:ι→Character)(Wslot:ι→ℝ→ℂ)(P M:ι→ℝ)
      (hP:∀i,0<P i)(hM:∀i,1≤M i)(aslot:ℝ)(haslot:0<aslot)
      (hsSlot:∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
      (hWslot:∀i x,‖Wslot i x‖≤M i)
      (t X₁ X₂ Y₁ Y₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)
      (hsame:Y₁*Y₂=X₁*X₂),X₁*X₂*(∏i,P i)≤Z^B→
    let inp:=naturalInput state p ha slots hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1) slots
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale≤
    2*physicalMass inp state.puncture 1 fixedBadMask 1 state.radial.profile state.radial.scale Z ξ/
      (X₁*X₂*∏i,P i)+
    2*Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
      Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) state.radial.profile*state.radial.scale*Z^ε+
    2*Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
      Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) state.radial.profile*state.radial.scale*Z^(-saving)+
    2*energy state.character state.mask 1 t (p.profile 0) (p.profile 1) slots
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale:=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,h⟩:=positive_first_physical_entry (ι:=ι)
    (fun _=>bslot) a b B ε ξ saving (fun _=>hbslot) ha hb hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro state p slots hp ν Wslot P M hP hM aslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame hV
  exact hZ.2 (naturalInput state p ha slots hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame) (p.profile 0) (p.profile 1) rfl rfl
    (p.support 0) (p.support 1) (fun _=>le_refl _) state.puncture state.radial hV
    (natural_inverse_scale state B hB)

end SevenEighths.CenteredMomentEnergyPhysicalEntry

end

end OAI
