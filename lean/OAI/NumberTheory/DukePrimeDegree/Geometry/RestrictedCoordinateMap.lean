import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Restrict

namespace OAI

/-! # Restricting an embedded coordinate measure inside a second chart -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

theorem map_restrict_comap_le
    {Y Z W : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
    (ν : Measure W) (f : Z → W) (hf : MeasurableEmbedding f)
    (g : Y → Z) (hg : MeasurableEmbedding g)
    (A : Set Y) (B : Set Z)
    (hsub : ∀ y ∈ A, g y ∈ B) :
    (((ν.comap (f ∘ g)).restrict A).map g) ≤ (ν.comap f).restrict B := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply hg.measurable hE,
    Measure.restrict_apply (hE.preimage hg.measurable),
    (hf.comp hg).comap_apply,
    Measure.restrict_apply hE,hf.comap_apply]
  apply measure_mono
  rintro _ ⟨y,⟨hyE,hyA⟩,rfl⟩
  exact ⟨g y,⟨hyE,hsub y hyA⟩,rfl⟩

end DukePrimeDegree

end

end OAI
