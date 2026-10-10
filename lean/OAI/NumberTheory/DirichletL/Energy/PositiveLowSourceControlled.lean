import OAI.NumberTheory.DirichletL.Energy.PositiveLowBandSource
import OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
import OAI.NumberTheory.DirichletL.Energy.LowBandEmpty

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled
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

open CenteredMomentEnergyPositiveLowBandSource (PhysicalLowAt)
open CenteredMomentEnergyBandMonotonicity

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical Cprevious:ℝ),
      1/6≤κ→0≤Cphysical→0≤Cprevious→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J S Cprevious→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)+Cprevious) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)+Cprevious) :=by
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hbound⟩:=
    CenteredMomentEnergyPositiveLowBandSource.actual_low_stages_from_physical (α:=α) M H hH
      W hW aslot bslot lo hi a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ
      hMcap hεdiag hξ
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical Cprevious hκ hCphysical hCprevious he hsave hold hmass
  let Cm:=Cphysical+Cprevious/Cfixed
  have hdiv:0≤Cprevious/Cfixed:=div_nonneg hCprevious hCfixed.le
  have hCm:0≤Cm:=by dsimp [Cm];positivity
  have hcc:Cphysical≤Cm:=by dsimp [Cm];linarith
  have heq:Cfixed*(Cm+1)=Cfixed*(Cphysical+1)+Cprevious:=by
    dsimp [Cm]
    field_simp
    ; ring
  have hprev:Cprevious≤Cfixed*(Cm+1):=by
    rw [heq]
    have hh:0≤Cfixed*(Cphysical+1):=by positivity
    linarith
  have hold':PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cm+1)):=
    positiveAt_transport (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z
      a b bΦ Bmask L rho e η₀ Q J J S (insert (0,0) S) Cprevious (Cfixed*(Cm+1)) hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.subset_insert _ _)
      hCprevious hprev hold
  have hmass':PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
      a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cm:=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤Z:=zero_le_one.trans hZ.1.le
    apply hh.trans
    gcongr
  have hh:=hZ.2 Bmask L Lslot rho κ e η₀ Q S J Cm hκ hCm he hsave hold' hmass'
  simpa only [heq] using hh

end SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled

end

end OAI
