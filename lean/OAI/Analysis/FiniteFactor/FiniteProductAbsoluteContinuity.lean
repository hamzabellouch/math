import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal
noncomputable section

/-- Replacing one independent coordinate is a measurable pushforward of a
single fresh draw and the original full product. -/
theorem infinitePi_update_law {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (ν : Measure X) [IsProbabilityMeasure ν] :
    (ν.prod (Measure.infinitePi μ)).map (fun z : X × (ι → X) => Function.update z.2 i z.1) =
      Measure.infinitePi (Function.update μ i ν) := by
  let : ∀ k, IsProbabilityMeasure (Function.update μ i ν k) := fun k => by
    by_cases hk : k = i
    · subst k; simpa using (inferInstance : IsProbabilityMeasure ν)
    · simpa [Function.update_of_ne hk] using (inferInstance : IsProbabilityMeasure (μ k))
  have hm : Measurable (fun z : X × (ι → X) => Function.update z.2 i z.1) := by
    apply Measurable.of_eval
    intro k
    by_cases hk : k = i
    · subst k; simpa using (measurable_fst : Measurable (Prod.fst : X × (ι → X) → X))
    · simpa [Function.update_of_ne hk,Function.comp_def] using (measurable_pi_apply k).comp
        (measurable_snd : Measurable (Prod.snd : X × (ι → X) → (ι → X)))
  apply Measure.eq_infinitePi
  intro S A hA
  rw [Measure.map_apply hm (MeasurableSet.pi S.countable_toSet (fun k _ => hA k))]
  by_cases hi : i ∈ S
  · have he : (fun z : X × (ι → X) => Function.update z.2 i z.1) ⁻¹' Set.pi (S : Set ι) A =
        A i ×ˢ Set.pi (↑(S.erase i) : Set ι) A := by
      ext z
      simp only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,mem_erase]
      constructor
      · intro hz
        refine ⟨by simpa using hz i hi,?_⟩
        intro k hk
        simpa [Function.update_of_ne hk.1] using hz k hk.2
      · rintro ⟨hz,hrest⟩ k hk
        by_cases hki : k = i
        · subst k; simpa using hz
        · simpa [Function.update_of_ne hki] using hrest k ⟨hki,hk⟩
    rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun k _ => hA k)]
    rw [← Finset.mul_prod_erase S (fun k => Function.update μ i ν k (A k)) hi]
    simp only [Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (mem_erase.mp hk).1]
  · have he : (fun z : X × (ι → X) => Function.update z.2 i z.1) ⁻¹' Set.pi (S : Set ι) A =
        Set.univ ×ˢ Set.pi (S : Set ι) A := by
      ext z
      simp only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Set.mem_univ,true_and]
      apply forall_congr'
      intro k
      constructor <;> intro h hk
      · simpa [Function.update_of_ne (show k ≠ i from fun he => hi (he ▸ hk))] using h hk
      · simpa [Function.update_of_ne (show k ≠ i from fun he => hi (he ▸ hk))] using h hk
    rw [he,Measure.prod_prod,measure_univ,one_mul,Measure.infinitePi_pi _ (fun k _ => hA k)]
    exact Finset.prod_congr rfl fun k hk => by
      rw [Function.update_of_ne (show k ≠ i from fun he => hi (he ▸ hk))]

/-- Absolute continuity survives finitely many coordinate changes. No assertion
about arbitrary infinite families of absolutely continuous marginals is used. -/
theorem infinitePi_ac_of_finite_changes {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (μ ν : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (F : Finset ι)
    (hac : ∀ i ∈ F, ν i ≪ μ i) (heq : ∀ i ∉ F, ν i = μ i) :
    Measure.infinitePi ν ≪ Measure.infinitePi μ := by
  induction F using Finset.induction_on generalizing ν with
  | empty =>
    have h : ν = μ := funext fun i => heq i (by simp)
    rw [h]
  | @insert i F hi ih =>
    let σ := Function.update ν i (μ i)
    let : ∀ k, IsProbabilityMeasure (σ k) := fun k => by
      by_cases hk : k = i
      · subst k; simpa [σ] using (inferInstance : IsProbabilityMeasure (μ i))
      · simpa [σ,Function.update_of_ne hk] using (inferInstance : IsProbabilityMeasure (ν k))
    have hσ : Measure.infinitePi σ ≪ Measure.infinitePi μ := by
      apply ih σ
      · intro k hk
        have hki : k ≠ i := fun h => hi (h ▸ hk)
        simpa [σ,Function.update_of_ne hki] using hac k (mem_insert_of_mem hk)
      · intro k hk
        by_cases hki : k = i
        · subst k; simp [σ]
        · simpa [σ,Function.update_of_ne hki] using heq k (by simp [hki,hk])
    have hupdate : Function.update σ i (ν i) = ν := by
      ext k
      by_cases hk : k = i <;> simp [σ,hk,Function.update_of_ne]
    have hsame : Function.update σ i (μ i) = σ := by simp [σ]
    have hprod := (hac i (mem_insert_self i F)).prod
      (Measure.AbsolutelyContinuous.rfl : Measure.infinitePi σ ≪ Measure.infinitePi σ)
    have hmap : ((ν i).prod (Measure.infinitePi σ)).map (fun z : X × (ι → X) => Function.update z.2 i z.1) ≪
        ((μ i).prod (Measure.infinitePi σ)).map (fun z : X × (ι → X) => Function.update z.2 i z.1) := by
      apply hprod.map
      apply Measurable.of_eval
      intro k
      by_cases hk : k = i
      · subst k; simpa using (measurable_fst : Measurable (Prod.fst : X × (ι → X) → X))
      · simpa [Function.update_of_ne hk,Function.comp_def] using (measurable_pi_apply k).comp
          (measurable_snd : Measurable (Prod.snd : X × (ι → X) → (ι → X)))
    rw [infinitePi_update_law,infinitePi_update_law,hupdate,hsame] at hmap
    exact hmap.trans hσ

end
end FiniteFactor

end OAI
