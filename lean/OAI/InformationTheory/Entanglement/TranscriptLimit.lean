import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory Topology
namespace SecretKey

theorem conditional_independence_limit {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (A B : MeasurableSpace Ω) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (h : ∀ k, CondIndep (F k) A B (F.le k) μ) :
    CondIndep (⨆ k, F k) A B (iSup_le fun k => F.le k) μ := by
  rw [condIndep_iff _ _ _ _ hA hB]
  intro s t hs ht
  have he : ∀ k, (μ⟦s ∩ t | F k⟧) =ᵐ[μ] (μ⟦s | F k⟧) * (μ⟦t | F k⟧) :=
    fun k => (condIndep_iff _ _ _ _ hA hB μ).mp (h k) s t hs ht
  have ha := MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := F) (s.indicator (fun _ => (1 : ℝ)))
  have hb := MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := F) (t.indicator (fun _ => (1 : ℝ)))
  have hab := MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := F) ((s ∩ t).indicator (fun _ => (1 : ℝ)))
  have hall := ae_all_iff.mpr he
  filter_upwards [ha,hb,hab,hall] with x hax hbx habx hex
  exact tendsto_nhds_unique habx ((hax.mul hbx).congr (fun k => (hex k).symm))
end SecretKey

end

end OAI
