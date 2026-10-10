import Mathlib
import OAI.Probability.SKGap.Brownian.ObservationPathEstimate
import OAI.Probability.SKGap.Localization.OperatorQuenched

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

def rawPathFailure (P : Measure Ω) (B : ℝ≥0→Ω→ℝ)
    (j A ε c ρ T : ℝ) (J : Disorder n) : ℝ :=
  ∑ σ : Spin n,mass J 0 σ*(Measure.pi (fun _ : Fin n=>P)).real
    {ω | ∃ t : ℝ≥0,(t:ℝ)≤T ∧ rootBad j A ε c ρ (coupling J) (observationField B σ t ω)}

lemma rawPathFailure_eq (P : Measure Ω) (B : ℝ≥0→Ω→ℝ)
    (j A K ε c ρ T : ℝ) (J : Disorder n) (hJ : operatorBound K (coupling J)) :
    rawPathFailure P B j A ε c ρ T J=pathFailure P B j A K ε c ρ T J := by
  simp only [rawPathFailure,pathFailure,conditionalPathFailure,hJ,true_and]

theorem quenched_stable_fields
    {P : Measure Ω} {B : ℝ≥0→Ω→ℝ}
    (hB : IsBrownianReal B P) {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
    ∃ A K ε c ρ a : ℝ, 1<A ∧ 2*β<K ∧ β*A<1 ∧
      0<ε ∧ 0<c ∧ 0<ρ ∧ 0<a ∧
      ∃ G : (n : ℕ)→Set (Disorder n),
        (∀ n,MeasurableSet (G n)) ∧
        Tendsto (fun n=>(disorderLaw β n).real (G n)) atTop (𝓝 1) ∧
        ∀ n, ∀ J ∈ G n,operatorBound K (coupling J) ∧
          rawPathFailure P B (β^2) A ε c ρ T J ≤ exp (-a*(n:ℝ)) := by
  obtain ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,V,hVm,hVn,hVp,hVt⟩ :=
    quenched_observation_path_stability hB hβ hβ1 hT
  let G : (n : ℕ)→Set (Disorder n) := fun n=>
    {J | operatorBound K (coupling J) ∧ V n J ≤ exp (-a*(n:ℝ))}
  have hnormMeas (n : ℕ) : MeasurableSet {J : Disorder n | operatorBound K (coupling J)} := by
    exact ((isClosed_operatorBound K).preimage continuous_coupling).measurableSet
  have hGm (n : ℕ) : MeasurableSet (G n) :=
    (hnormMeas n).inter (measurableSet_le (hVm n) measurable_const)
  have hcompl (n : ℕ) : (G n)ᶜ = {J | ¬operatorBound K (coupling J)}∪
      {J | exp (-a*(n:ℝ))<V n J} := by
    ext J
    simp only [G,mem_compl_iff,mem_ofPred_eq,not_and_or,not_le,mem_union]
  have hbad : Tendsto (fun n=>(disorderLaw β n).real (G n)ᶜ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>measureReal_nonneg)
      (fun n=>?_)
      (by simpa only [add_zero] using (quenched_operator_bound hβ hK).add hVt)
    rw [hcompl]
    exact measureReal_union_le _ _
  refine ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,G,hGm,?_,?_⟩
  · have hh : Tendsto (fun n=>1-(disorderLaw β n).real (G n)ᶜ) atTop (𝓝 (1-0)) :=
      tendsto_const_nhds.sub hbad
    have he (n : ℕ) : (disorderLaw β n).real (G n)=1-(disorderLaw β n).real (G n)ᶜ := by
      rw [measureReal_compl (hGm n),probReal_univ]
      ring
    simpa only [sub_zero,←he] using hh
  · intro n J hJ
    refine ⟨hJ.1,?_⟩
    rw [rawPathFailure_eq P B (β^2) A K ε c ρ T J hJ.1]
    exact (hVp n J).trans hJ.2
end SKGap.ObservationBridge

end
end

end OAI
