import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter

theorem exists_measurable_glue_of_local_L2 {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : ℕ → Set X) (hs : ∀ H, MeasurableSet (s H))
    (hcover : ∀ x, ∃ H, x ∈ s H) (v : ℕ → X → ℝ)
    (hv : ∀ H, Measurable (v H)) (hL2 : ∀ H, MemLp (v H) 2 (ν.restrict (s H)))
    (hcompat : ∀ H K, v H =ᵐ[ν.restrict (s H ∩ s K)] v K) :
    ∃ f : X → ℝ, Measurable f ∧ ∀ H,
      f =ᵐ[ν.restrict (s H)] v H ∧ MemLp f 2 (ν.restrict (s H)) := by
  classical
  let f : X → ℝ := fun x => v (Nat.find (hcover x)) x
  have hfm : Measurable f := Measurable.find (p := fun n x => x ∈ s n) hv hs hcover
  have heq : ∀ H, f =ᵐ[ν.restrict (s H)] v H := by
    intro H
    apply (ae_restrict_iff' (hs H)).mpr
    have hgood : ∀ᵐ x ∂ν, ∀ K, x ∈ s K ∩ s H → v K x = v H x :=
      ae_all_iff.mpr (fun K => (ae_restrict_iff' ((hs K).inter (hs H))).mp (hcompat K H))
    filter_upwards [hgood] with x hx
    intro hxH
    exact hx (Nat.find (hcover x)) ⟨Nat.find_spec (hcover x), hxH⟩
  exact ⟨f, hfm, fun H => ⟨heq H, (memLp_congr_ae (heq H)).mpr (hL2 H)⟩⟩

theorem ae_eq_of_countable_local_agreement {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : ℕ → Set X) (hs : ∀ H, MeasurableSet (s H))
    (hcover : ∀ x, ∃ H, x ∈ s H) (f g : X → ℝ)
    (heq : ∀ H, f =ᵐ[ν.restrict (s H)] g) : f =ᵐ[ν] g := by
  have hgood : ∀ᵐ x ∂ν, ∀ H, x ∈ s H → f x = g x :=
    ae_all_iff.mpr (fun H => (ae_restrict_iff' (hs H)).mp (heq H))
  filter_upwards [hgood] with x hx
  obtain ⟨H, hxH⟩ := hcover x
  exact hx H hxH

end

end RieszRectifiability

end OAI
