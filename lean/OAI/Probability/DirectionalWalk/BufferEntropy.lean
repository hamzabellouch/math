import OAI.Probability.DirectionalWalk.EntropyLaws

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section BufferEntropy
variable {Λ Θ B G : Type*} [Countable Λ] [Countable Θ] [Countable B] [Countable G]
  [MeasurableSpace Λ] [MeasurableSpace Θ] [MeasurableSpace B] [MeasurableSpace G]
  [MeasurableSingletonClass Λ] [MeasurableSingletonClass Θ] [MeasurableSingletonClass B]
  [MeasurableSingletonClass G] [AddCommGroup G]

omit [Countable Θ] in

lemma buffer_remaining_count_entropy (π : Measure (ℕ × G)) (ρ : Measure Λ)
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (H : Λ → Θ) (D : Λ → G) (C : Λ → ℕ) :
    conditionedEntropy (π.prod ρ) (fun ω => ω.1.1+C ω.2)
      (fun ω => ((H ω.2,ω.2),ω.1.2+D ω.2)) =
      conditionedEntropy π Prod.fst Prod.snd := by
  let μ := π.prod ρ
  have he : conditionedInformation μ (fun ω => ω.1.1+C ω.2)
      (fun ω => ((H ω.2,ω.2),ω.1.2+D ω.2)) =
      conditionedInformation μ (fun ω => ω.1.1) (fun ω => (ω.1.2,ω.2)) := by
    rw [conditionedInformation_same_conditioner μ (fun ω => ω.1.1+C ω.2)
      (fun ω => ((H ω.2,ω.2),ω.1.2+D ω.2)) (fun ω => (ω.1.2,ω.2)) (by
        intro ω ξ
        simp only [Prod.mk.injEq]
        constructor
        · rintro ⟨⟨_,h⟩,hd⟩
          exact ⟨add_right_cancel (by simpa only [h] using hd),h⟩
        · rintro ⟨hd,h⟩
          simp only [hd,h,and_self])]
    exact conditionedInformation_fiberwise_injective μ (fun ω => ω.1.1)
      (fun ω => (ω.1.2,ω.2)) (fun y x => x+C y.2) (fun _ _ _ h => Nat.add_right_cancel h)
  change (∫ ω, _ ∂μ) = _
  rw [he]
  change conditionedEntropy μ (fun ω => ω.1.1) (fun ω => (ω.1.2,ω.2)) = _
  rw [conditionedEntropy_indep_pair μ (fun ω => ω.1.1) (fun ω => ω.1.2) Prod.snd
    (indepFun_prod (measurable_of_countable (fun p : ℕ × G => (p.2,p.1))) measurable_id)]
  exact conditionedEntropy_prod_fst π ρ Prod.fst Prod.snd

lemma buffer_displacement_entropy (π : Measure (ℕ × G)) (ρ : Measure Λ)
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ] (H : Λ → Θ) (D : Λ → G) :
    conditionedEntropy (π.prod ρ) (fun ω => ω.1.2+D ω.2) (fun ω => (H ω.2,ω.2)) =
      entropyOf π Prod.snd := by
  have he := conditionedInformation_fiberwise_injective (π.prod ρ) (fun ω => ω.1.2)
    (fun ω => (H ω.2,ω.2)) (fun y x => x+D y.2) (fun _ _ _ h => add_right_cancel h)
  change (∫ ω, _ ∂π.prod ρ) = _
  rw [he]
  change conditionedEntropy (π.prod ρ) (fun ω => ω.1.2) (fun ω => (H ω.2,ω.2)) = _
  rw [conditionedEntropy_indep _ _ _ (indepFun_prod measurable_snd
    (measurable_of_countable (fun x => (H x,x))))]
  exact entropyOf_prod_fst π ρ Prod.snd

lemma buffer_entropy_chain (π : Measure (ℕ × G)) (ρ : Measure Λ)
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (H : Λ → Θ) (Bfun : Λ → B) (DA : Λ → G) (DB : B → G) (C : Λ → ℕ)
    (hT : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.1+C ω.2)) (π.prod ρ))
    (hS : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.2+DA ω.2+DB (Bfun ω.2))) (π.prod ρ))
    (D₀ : ℝ)
    (hI : conditionedEntropy (π.prod ρ) (fun ω => ω.1.2+DA ω.2) (fun ω => H ω.2) -
      conditionedEntropy (π.prod ρ) (fun ω => ω.1.2+DA ω.2) (fun ω => (H ω.2,Bfun ω.2)) ≤ D₀) :
    conditionedEntropy (π.prod ρ) (fun ω => ω.1.2+DA ω.2) (fun ω => H ω.2) +
      conditionedEntropy π Prod.fst Prod.snd ≤ D₀ +
      entropyOf (π.prod ρ) (fun ω => (ω.1.2+DA ω.2+DB (Bfun ω.2),ω.1.1+C ω.2)) := by
  let μ := π.prod ρ
  let Z := fun ω : (ℕ × G) × Λ => ω.1.2+DA ω.2
  let T := fun ω : (ℕ × G) × Λ => ω.1.1+C ω.2
  let S := fun ω : (ℕ × G) × Λ => Z ω+DB (Bfun ω.2)
  let F := fun ω : (ℕ × G) × Λ => (H ω.2,Bfun ω.2)
  let K := fun ω : (ℕ × G) × Λ => ((H ω.2,ω.2),Z ω)
  have hpair := integrable_informationOf_pair μ S T hS hT
  have hup := conditionedEntropy_le_entropyOf μ (fun ω => (S ω,T ω)) F hpair
  rw [conditionedEntropy_chain μ S T F (integrable_conditionedInformation μ S F hS)
    (integrable_conditionedInformation μ T (fun ω => (F ω,S ω)) hT)] at hup
  have hs : conditionedEntropy μ S F = conditionedEntropy μ Z F := by
    apply congrArg (fun f => ∫ ω, f ω ∂μ)
      (conditionedInformation_fiberwise_injective μ Z F
        (fun y x => x+DB y.2) (fun _ _ _ h => add_right_cancel h))
  have ht : conditionedEntropy μ T K ≤ conditionedEntropy μ T (fun ω => (F ω,S ω)) := by
    exact conditionedEntropy_monotone_function μ T K
      (fun k => ((k.1.1,Bfun k.1.2),k.2+DB (Bfun k.1.2))) hT
  have hk : conditionedEntropy μ T K = conditionedEntropy π Prod.fst Prod.snd :=
    buffer_remaining_count_entropy π ρ H DA C
  rw [hs] at hup
  rw [hk] at ht
  change conditionedEntropy μ Z (fun ω => H ω.2) - conditionedEntropy μ Z F ≤ D₀ at hI
  change conditionedEntropy μ Z (fun ω => H ω.2) + _ ≤ D₀ + entropyOf μ (fun ω => (S ω,T ω))
  linarith
end BufferEntropy

end DirectionalZeroOne

end OAI
