import OAI.Geometry.RCD.Transport.ObservableSubplans
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace OAI

/-! # A subplan retains the original density along an invertible observable -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem rnDeriv_restricted_map_ae (π : Measure A) [IsFiniteMeasure π]
    (μ : Measure B) [SigmaFinite μ] {f : A → B} {g : B → A}
    (hf : Measurable f) (hg : Measurable g) (hinv : ∀ᵐ a ∂π, g (f a)=a)
    (hac : π.map f ≪ μ) {S : Set A} (hS : MeasurableSet S) :
    ∀ᵐ a ∂π.restrict S, ((π.restrict S).map f).rnDeriv μ (f a)=(π.map f).rnDeriv μ (f a) := by
  have hE := hS.preimage hg
  have hr := Measure.rnDeriv_restrict (π.map f) μ hE
  rw [←restrict_map_of_ae_left_inverse π hf hg hinv hS] at hr
  have hsub : (π.restrict S).map f ≪ μ :=
    (Measure.map_mono Measure.restrict_le_self hf).absolutelyContinuous.trans hac
  have hpull := ae_of_ae_map (μ:=π.restrict S) hf.aemeasurable (hr.filter_mono hsub.ae_le)
  filter_upwards [hpull,hinv.filter_mono Measure.restrict_le_self.absolutelyContinuous.ae_le,
    ae_restrict_mem hS] with a ha hi hs
  simpa only [indicator_of_mem (show f a ∈ g ⁻¹' S by simpa only [mem_preimage,hi] using hs)] using ha

end RegularPointCoordinates

end

end OAI
