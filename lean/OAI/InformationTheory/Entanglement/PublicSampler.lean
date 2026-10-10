import OAI.InformationTheory.Entanglement.IndependentTapes

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey
variable {Ω S T Y : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
variable [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Y]
variable [StandardBorelSpace Y] [Nonempty Y]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [StandardBorelSpace Y] [Nonempty Y] in
theorem sampled_public_independence
    {F A : MeasurableSpace Ω} (hF : F ≤ mΩ) (_ : A ≤ mΩ)
    (H : Ω → S) (hH : @Measurable Ω S mΩ _ H)
    (hFH : F ≤ (inferInstance : MeasurableSpace S).comap H)
    (hAH : A ≤ (inferInstance : MeasurableSpace S).comap H)
    (g : S → T) (hg : Measurable g) (hpub : Measurable[F] (g ∘ H))
    (U : Ω → I) (hU : @Measurable Ω I mΩ _ U) (hind : IndepFun H U μ)
    (hUlaw : @Measure.map Ω I mΩ _ U μ=volume)
    (κ : Kernel T Y) [IsMarkovKernel κ]
    (f : T → I → Y) (hf : Measurable (uncurry f))
    (hmap : ∀ t, volume.map (f t)=κ t) :
    CondIndep F A ((inferInstance : MeasurableSpace Y).comap (fun ω => f (g (H ω)) (U ω))) hF μ := by
  let : MeasurableSpace Ω := mΩ
  have hC : @Measurable Ω Y mΩ _ (fun ω => f (g (H ω)) (U ω)) :=
    hf.comp ((hg.comp hH).prodMk hU)
  apply independent_of_public_conditional_laws hF hH.comap_le hFH hAH hC.comap_le
  intro b hb
  obtain ⟨E,hE,rfl⟩ := hb
  have hs := sampled_conditional_event H U hH hU hind (fun s u => f (g s) u)
    (hf.comp ((hg.comp measurable_fst).prodMk measurable_snd)) (κ.comap g hg)
    (by intro s; simpa only [hUlaw,Kernel.comap_apply] using hmap (g s)) E hE
  have hm : StronglyMeasurable[F] (fun ω => (κ (g (H ω))).real E) := by
    exact (((κ.measurable_coe hE).comp hpub).ennreal_toReal).stronglyMeasurable
  exact hm.aestronglyMeasurable.congr hs.symm

end SecretKey

end

end OAI
