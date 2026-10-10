import OAI.NumberTheory.DirichletL.Energy.LowFixedRadialEntry
import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyLowFixedRadialEntry CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentAmplificationChildInput CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=
  CenteredMomentEnergyOriginalSource.energyOriginalSourceDecidableSum

section Source
variable (Q:Ideal O)[NeZero Q]
variable (H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤H)
variable (η₀:Character)(θ:ι→RayQuotient.Characters Q H)
variable (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:ι→ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def sourceInput : Input ι :=
  input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
    state p ha t X₁ X₂ X₁ X₂ hX₁ hX₂ hX₁ hX₂ rfl

def zeroSourceInput : Input ι :=
  zeroInput (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂)
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 1))
end Source

private lemma control_mono {a b:ℝ}(p:Profiles a b)(S:Finset (ℕ×ℕ)):
    p.control S≤p.control (insert (0,0) S):=by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem natural_low_source_bound
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃Cfixed:ℝ,0<Cfixed ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Q:Ideal O)[NeZero Q](H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤H),
    ∀(η₀:Character)(θ:ι→RayQuotient.Characters Q H),
    ∀(w σ freq:ι→ℝ), (∀i,0≤w i) → ∀hσ:∀i,σ i∈Set.Icc lo hi,
    ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(t X₁ X₂:ℝ),
    ∀hX₁:0<X₁,∀hX₂:0<X₂,∀κ:ℝ,1/6≤κ →
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤Mcap →
    ∀(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical height e:ℝ),0≤Cphysical →0≤height →
    εdiag≤e → -saving≤e →
    physicalMass (zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) state.puncture 1 fixedBadMask 1
      Ψ state.radial.scale Z ξ /
      volume (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) ≤
      Cphysical*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e) →
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool Q H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I*
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i=>Z^(w i)) X₁ X₂ state.radial.keep state.radial.profile state.radial.scale ≤
      Cfixed*(Cphysical+1)*diagonalControl state.radial.profile*
        (p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e):=by
  obtain ⟨Ψ,hΨs,hΨn,Sd,St,Cd,Ct,hCd,hCt,hred⟩:=
    original_low_reduction (ι:=ι) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving
      (fun _=>hbslot) ha hb hMcap hεdiag hξ
  let P:ℝ:=(profileBound W hW aslot bslot lo hi haslot hWs)^(2*Fintype.card ι)
  let D:ℝ:=Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=pow_nonneg (zero_le_one.trans (profileBound_ge_one W hW aslot bslot lo hi haslot hWs)) _
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  refine ⟨Ψ,hΨs,hΨn,2*(1+D+T),by positivity,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro Q _ H hH η₀ θ w σ freq hw hσ Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ hcap
    S J Cphysical height e hCphysical hheight he hsave hphysical
  let s:=sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
  have hZ:0<Z:=zero_lt_one.trans hz.1
  have hPi:∀i,1≤s.P i:=fun i=>Real.one_le_rpow hz.1.le (hw i)
  have hv:volume s≤Z^Mcap:=original_volume_cap s Z κ Mcap hz.1 hκ hPi (by
    change length Z X₁+length Z X₂+6*κ*(∑i,Real.logb Z (Z^(w i)))≤Mcap
    simpa only [Real.logb_rpow hZ hz.1.ne'] using hcap)
  have hscale:1≤state.radial.scale:=by rw [state.scale_eq];exact Real.one_le_rpow hz.1.le state.row_nonneg
  have hKi:state.radial.scale⁻¹≤Z^Mcap:=
    (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow hz.1.le hMcap)
  have hbound:=hz.2 s (p.profile 0) (p.profile 1) rfl rfl (p.support 0) (p.support 1)
    (fun _=>le_rfl) state.puncture state.radial state.radial_support hv hKi
  have hplain:(plainControl s (p.profile 0) (p.profile 1))^2≤P*(p.control (insert (0,0) S))^2:=
    plain_control_sq_le s p S (Fintype.card ι) _
      (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) le_rfl (fun _=>le_rfl)
  have hsquare:(p.control S)^2≤(p.control (insert (0,0) S))^2:=
    pow_le_pow_left₀ (p.control_nonneg S) (control_mono p S) 2
  let F:ℝ:=(p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e)
  have hF:0≤F:=by dsimp [F];positivity
  have hheight1:1≤(1+|t|+height)^J:=one_le_pow₀ (by linarith [abs_nonneg t])
  have hscalePower (x:ℝ)(hx:x≤e):state.radial.scale*Z^x≤Z^(state.width+e):=by
    rw [state.scale_eq,←Real.rpow_add hZ]
    exact Real.rpow_le_rpow_of_exponent_le hz.1.le (by unfold NaturalState.width;linarith [state.character_nonneg])
  have hphysical':physicalMass (zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) state.puncture 1 fixedBadMask 1
      Ψ state.radial.scale Z ξ/volume s≤Cphysical*F:=by
    apply hphysical.trans
    calc
      _≤Cphysical*(p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e):=by gcongr
      _=Cphysical*F:=by dsimp [F];ring
  have hterm (c A x:ℝ)(hc:0≤c)(hA:0≤A)(hx:x≤e):
      c*(plainControl s (p.profile 0) (p.profile 1))^2*A*state.radial.scale*Z^x≤c*P*A*F:=by
    calc
      _≤c*(P*(p.control (insert (0,0) S))^2)*A*(state.radial.scale*Z^x):=by
        rw [←mul_assoc];gcongr
      _≤c*(P*(p.control (insert (0,0) S))^2)*A*Z^(state.width+e):=by
        gcongr;exact hscalePower x hx
      _≤c*P*A*F:=by
        have hh:=le_mul_of_one_le_right
          (show 0≤c*P*A*(p.control (insert (0,0) S))^2*Z^(state.width+e) by positivity) hheight1
        dsimp [F]
        convert hh using 1 <;> ring
  have hd:=hterm Cd (Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) he
  have ht:=hterm Ct (St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) hsave
  change energy state.character state.mask 1 t (p.profile 0) (p.profile 1) _ _ _ _ _ _ _ _≤_ at hbound
  apply hbound.trans
  change 2*diagonalControl state.radial.profile*(_+_+_)≤_
  have hsum:=add_le_add (add_le_add hphysical' hd) ht
  have hmul:=mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg state.radial.profile))
  apply hmul.trans
  dsimp only [D,T] at *
  have hcoeff:Cphysical+Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ+
      Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ≤
      (1+Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ+
        Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ)*(Cphysical+1):=by
    nlinarith [mul_nonneg hCphysical hD,mul_nonneg hCphysical hT]
  have hh:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff hF)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg state.radial.profile))
  dsimp [F] at hh ⊢
  nlinarith only [hh]

end SevenEighths.CenteredMomentEnergyNaturalLowSourceBound

end

end OAI
