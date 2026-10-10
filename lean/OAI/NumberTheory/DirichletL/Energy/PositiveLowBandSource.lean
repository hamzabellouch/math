import OAI.NumberTheory.DirichletL.Energy.NaturalLowSourceBound
import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
import OAI.NumberTheory.DirichletL.Energy.LowBandEmpty

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowBandSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PhysicalLowAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤state.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*state.width/6→
    physicalMass (zeroSourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)
      state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ /
      volume (sourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical:ℝ),
      1/6≤κ→0≤Cphysical→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1))→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)):=by
  have hfixed (T:Finset α):=natural_low_source_bound (ι:=T) W hW aslot bslot lo hi
    a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ hMcap hεdiag hξ
  choose Ψ hΨs hΨn Cj hCj hbound using hfixed
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0<Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical hκ hCphysical he hsave hold hmass
  have hpositive:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cphysical+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidth
      p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    by_cases hsmall:state.width≤ rho
    · exact hold T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
        state hQ hsmall p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
    have hp:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      state hQ (le_of_not_ge hsmall) hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    have hh:=(hZ T).2 M H hH η₀ θ w σ freq hw (fun i=>⟨hσlo i,hσhi i⟩)
      Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ (hcapacity.trans hwidth)
      S J Cphysical height e hCphysical hheight he hsave hp
    have hc:=hCC T
    have hd:=diagonalControl_nonneg state.radial.profile
    have hz:0≤Z:=zero_le_one.trans hZ1.le
    apply hh.trans
    gcongr
  exact ⟨hpositive,CenteredMomentEnergyLowBandEmpty.positive_low_zero (α:=α) M H hH
    W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J (insert (0,0) S)
    (Cfixed*(Cphysical+1)) hpositive⟩

end SevenEighths.CenteredMomentEnergyPositiveLowBandSource

end

end OAI
