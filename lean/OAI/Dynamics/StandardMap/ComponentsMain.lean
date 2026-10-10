import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.EntropyLyapunov
import OAI.Dynamics.StandardMap.Coding.PositiveWeakBernoulliRate
import OAI.Dynamics.StandardMap.Coding.CenteredDecoder

namespace OAI

section
namespace StandardMapEntropy
open MeasureTheory Set Filter HyperbolicCoding Entropy
open scoped BigOperators ENNReal Topology

theorem actual_return_bernoulli (k : ℝ) (hk : 0≤k) (N : ℕ)
    (E : Set Torus) (hE : 0 < area E)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (((standardMap k)^[N])^[m]) (normalizedArea E))
    (α : ℕ → ℕ → Torus → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun z => fun i j => α i j z))
    (hwb : ∀ M : ℕ,WeakBernoulliProcess (normalizedArea E)
      (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M)) :
    IsBernoulli ((standardMap k)^[N]) (normalizedArea E) := by
  let := normalizedArea_probability hE
  let := normalizedArea_nullSingleton E
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have he : Ergodic e (normalizedArea E) := by
    rw [heq]
    simpa only [Function.iterate_one] using htotal 1 (by omega)
  have het : ∀ m : ℕ,0 < m → Ergodic (e^[m]) (normalizedArea E) := by simpa only [heq] using htotal
  obtain ⟨n,β,p₀,hβ,hβsum,hβentropy,hp₀,H,hcode₀,_hr,_hshift,_hjoint⟩ :=
    actual_return_full_entropy_iid_factor k hk N E hE htotal α hα hsep hwb
  have Hβ : FiniteRateSupremum (normalizedArea E) e (weightEntropy β) := by simpa only [heq] using H
  let zero : Fin (n+2) := ⟨0,by omega⟩
  let one : Fin (n+2) := ⟨1,by omega⟩
  have h01 : zero≠one := by
    intro h
    have hv : (0 : ℕ)=1 := congrArg Fin.val h
    omega
  obtain ⟨p,hp,hcode,hdecode⟩ := generating_iid_partition (normalizedArea E) e he het
    β hβ hβsum hβentropy Hβ α hα hsep hwb zero one h01 p₀ hp₀ hcode₀
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hm := bernoulli_model_of_generating_iid (normalizedArea E) e p hp (finiteWeightLaw β) hcode α hsep hdecode
  simpa only [IsBernoulli,heq] using hm
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped ENNReal

theorem main_components : MainComponentsObligation := by
  obtain ⟨K,hK,hpieces⟩ := eventually_actual_cyclic_weakBernoulli_component
  refine ⟨K,hK,?_⟩
  intro k hk
  obtain ⟨E,hE,hEpos,hEinv,hEerg,hEspec,N,hN,P,hPM,hPU,hPD,hPC,hPA,hPT,hPW⟩ := hpieces k hk
  refine ⟨E,hE,hEpos,?_,hEerg,hEspec,N,hN,P,hPM,hPU,hPD,hPC,hPA,?_⟩
  · exact Filter.EventuallyEq.of_eq hEinv
  · intro j
    obtain ⟨α,hα,hsep,hwb⟩ := hPW j
    exact actual_return_bernoulli k (hK.le.trans hk) N (P j) (hPA j).2
      (hPT j) α hα hsep hwb

end StandardMapEntropy

end

end OAI
