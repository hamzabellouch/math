import Mathlib.Probability.Martingale.Basic

namespace OAI

noncomputable section
open MeasureTheory Filter Set

namespace Problem367.MartingalePushforward

 theorem martingale_of_pullback
    {ι Ω Ξ : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {φ : Ω → Ξ} (hφ : MeasurePreserving φ μ ν)
    {F : Filtration ι mΩ} {G : Filtration ι mΞ}
    (hpast : ∀ t, (G t).comap φ ≤ F t)
    {X : ι → Ξ → ℝ} (hX : StronglyAdapted G X)
    (hM : Martingale (fun t ω => X t (φ ω)) F μ) : Martingale X G ν := by
  have hm (t : ι) : AEStronglyMeasurable (X t) ν :=
    ((hX t).mono (G.le t)).aestronglyMeasurable
  have hi (t : ι) : Integrable (X t) ν :=
    (hφ.integrable_comp (hm t)).mp (hM.integrable t)
  refine ⟨hX, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (G.le s) (hi t)
    (fun A _ _ => (hi s).integrableOn) _ (hX s).aestronglyMeasurable
  intro A hA _
  have hpre : MeasurableSet[F s] (φ ⁻¹' A) :=
    hpast s _ ((comap_measurable (m := G s) φ) hA)
  have he (u : ι) : (∫ x in A, X u x ∂ν) = ∫ ω in φ ⁻¹' A, X u (φ ω) ∂μ := by
    rw [← hφ.map_eq]
    exact setIntegral_map (G.le s _ hA) (by simpa only [hφ.map_eq] using hm u)
      hφ.measurable.aemeasurable
  rw [he s, he t]
  exact hM.setIntegral_eq hst hpre

end Problem367.MartingalePushforward

end

end OAI
