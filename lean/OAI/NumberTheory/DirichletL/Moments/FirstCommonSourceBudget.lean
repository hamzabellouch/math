import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocatedInput
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocationControl

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonSourceBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

lemma child_nonneg (s:Input ι)(C R seed:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hW:∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re):
    0≤childNormalizedGaussSource s C R seed B τ t W K:=by
  rw [←allocated_input_energy s C R seed seed B τ t W K]
  apply div_nonneg
  · exact allocated_nonneg (original s R seed) C seed B τ t W K hK hW
  · rw [allocated_input_volume s C R seed seed B τ t]
    exact (CenteredMomentAmplificationChildInput.volume_pos _).le

theorem common_energy_live_allocations (N:ℕ)(a b:ℝ)(ha:0<a)
    (s:Input ι)(hcard:Fintype.card ι≤N)(haS:a≤s.lower)(hbS:s.upper≤b)
    (C R seed:Ideal O)(hC:Supported C)(hseed:seed∣C)
    (τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hW:∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re):
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
    (max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
      ∑B:actualAllocations s.pools C,
        if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
          (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
        else 0:=by
  have hh:=normalized_common_energy_allocation (original s R seed) s.pools_ne s.prime C hC hseed
    τ t L W K hK hW s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos
  rw [←commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change _ ≤ ((actualAllocations s.pools C).card:ℝ)*
    ∑B:actualAllocations s.pools C,
      (‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
        (allocatedEnergy (original s R seed) C L B τ t W K/
          rawVolume (allocatedData (original s R seed) C L B)) at hh
  simp_rw [allocated_input_energy s C R seed L _ τ t W K] at hh
  apply hh.trans
  calc
    _≤((actualAllocations s.pools C).card:ℝ)*
      ∑B:actualAllocations s.pools C,
        ((max 1 b)^N/(C.absNorm:ℝ))*
          (if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
            (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
          else 0):=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      by_cases hz:frozenCoefficient B.val C R s.ν s.W s.P=0
      · simp only [hz,ne_eq,not_true_eq_false,ite_false,norm_zero,zero_pow (by decide:2≠0),zero_div,zero_mul,mul_zero]
        exact le_rfl
      · rw [ite_eq_left hz]
        have hf:=frozen_normalized_bound N a b ha (original s R seed) hcard C hC.1 B s.M
          (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.ν_bound s.W_bound
          (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
        have hn:=child_nonneg s C R L B τ t W K hK hW
        change ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P≤
          (max 1 b)^N/(C.absNorm:ℝ)*(frozenControl B.val s.M)^2 at hf
        convert mul_le_mul_of_nonneg_right hf hn using 1 ; ring
    _=_:=by rw [←Finset.mul_sum];ring

theorem common_energy_from_live_children (N:ℕ)(a b ε:ℝ)(ha:0<a)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{κ:Type*}[Fintype κ],∀s:Input κ,
    Fintype.card κ≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0<K → 0≤E →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤E*(∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*E*(∏i,s.M i)^2:=by
  obtain ⟨D,hD,hmass⟩:=allocated_control_mass N ε hε
  refine ⟨(max 1 b)^N*D,mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hD,?_⟩
  intro κ _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hh:=common_energy_live_allocations N a b ha s hcard haS hbS C R seed hC hseed τ t L W K hK hW
  apply hh.trans
  have hc:0≤(max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ):=by positivity
  have hs:(∑B:actualAllocations s.pools C,
      if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
        (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K else 0)≤
      E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B hB
    split_ifs with hb
    · convert mul_le_mul_of_nonneg_left (hchild B hb) (sq_nonneg (frozenControl B.val s.M)) using 1 ; ring
    · positivity
  have hm:=hmass hcard s C R hC.1 τ t
  calc
    _≤((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ))*
        (E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=
      mul_le_mul_of_nonneg_left hs hc
    _=((max 1 b)^N*E)*(((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
        ∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=by ring
    _≤((max 1 b)^N*E)*(D*(C.absNorm:ℝ)^(ε-1)*(∏i,s.M i)^2):=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by positivity) hE)
    _=_:=by ring

end SevenEighths.CenteredMomentFirstCommonSourceBudget

end

end OAI
