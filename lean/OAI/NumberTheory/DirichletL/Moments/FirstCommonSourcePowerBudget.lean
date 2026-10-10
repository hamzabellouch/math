import OAI.NumberTheory.DirichletL.Moments.FirstCommonSourceBudget
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonSourcePowerBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
local notation "O"=>ActualEisensteinCubic.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem common_energy_power_budget (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ),0<K →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(CenteredMomentAmplificationChildInput.volume (child s C R B τ t))^(α j))*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*
          (∑j,E j*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))^(α j))*
            (∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound,hCbound,?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  apply hbound s hcard haS hbS C R seed hC hseed τ t L W K _ hK
    (Finset.sum_nonneg (fun j _=>mul_nonneg (hE j) (Real.rpow_nonneg (by positivity) _))) hW
  intro B hB
  apply (hchild B hB).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hE j)
  exact Real.rpow_le_rpow (CenteredMomentAmplificationChildInput.volume_pos _).le
    (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) (hα j)

theorem common_energy_linear_volume (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0<K → 0≤E →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        E*CenteredMomentAmplificationChildInput.volume (child s C R B τ t)*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-2)*CenteredMomentAmplificationChildInput.volume s*E*(∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound*b^N,mul_pos hCbound (pow_pos (zero_lt_one.trans_le hb) _),?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  have hh:=hbound s hcard haS hbS C R seed hC hseed τ t L W K
    (E*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))) hK
    (mul_nonneg hE (by positivity)) hW (fun B hB=>by
      apply (hchild B hB).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) hE)
        (sq_nonneg _))
  apply hh.trans_eq
  have hp:(C.absNorm:ℝ)^(ε-2)=(C.absNorm:ℝ)^(ε-1)/(C.absNorm:ℝ):=by
    rw [show ε-2=(ε-1)-1 by ring,Real.rpow_sub hn,Real.rpow_one]
  rw [hp]
  ring

end SevenEighths.CenteredMomentFirstCommonSourcePowerBudget

end

end OAI
