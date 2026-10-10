import OAI.Analysis.KadisonKastler.HilbertCoefficientMeasurable
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Translation-invariant measurable fields are constant

For each translation the exceptional null set may differ. Fubini and the
measure-preserving shear `(s,t) ↦ (s-t,t)` nevertheless give a single
almost-everywhere constant representative. The operator-valued version
uses only countably many dense Hilbert coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A measurable scalar function invariant under every real translation
as an almost-everywhere class is almost everywhere constant. -/
theorem measurable_real_translation_invariant_const (f : ℝ → ℂ)
    (hf : Measurable f)
    (htrans : ∀ s : ℝ, (fun t => f (t + s)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  have hm : MeasurableSet {p : ℝ × ℝ | f (p.1 + p.2) = f p.2} :=
    measurableSet_eq_fun (hf.comp (measurable_fst.add measurable_snd))
      (hf.comp measurable_snd)
  have hp : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f (p.1 + p.2) = f p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) hm).mpr
    apply Eventually.of_forall
    intro s
    change ∀ᵐ y : ℝ ∂(volume : Measure ℝ), f (s + y) = f y
    filter_upwards [htrans s] with t ht
    simpa only [add_comm] using ht
  have hp' : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f p.1 = f p.2 := by
    have h := (measurePreserving_sub_prod (volume : Measure ℝ) volume).quasiMeasurePreserving.ae hp
    simpa only [sub_add_cancel] using h
  obtain ⟨s, hs⟩ := (Measure.ae_ae_of_ae_prod hp').exists
  exact ⟨f s, hs.mono fun _ h => h.symm⟩

/-- The same conclusion for a scalar almost-everywhere measurable class. -/
theorem aestronglyMeasurable_real_translation_invariant_const (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume)
    (htrans : ∀ s : ℝ, (fun t => f (t + s)) =ᵐ[volume] f) :
    ∃ c : ℂ, f =ᵐ[volume] fun _ => c := by
  have hmk (s : ℝ) : (fun t => hf.mk f (t + s)) =ᵐ[volume] hf.mk f := by
    have hshift := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae_eq_comp
      hf.ae_eq_mk
    filter_upwards [hshift, htrans s, hf.ae_eq_mk] with t hshift ht hbase
    exact hshift.symm.trans (ht.trans hbase)
  obtain ⟨c, hc⟩ := measurable_real_translation_invariant_const
    (hf.mk f) hf.measurable_mk hmk
  exact ⟨c, hf.ae_eq_mk.trans hc⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

/-- Scalar translation invariance of a weakly measurable operator field
implies a single almost-everywhere constant bounded operator. No common
exceptional set for the original uncountable family of translations is
required. -/
theorem operatorField_real_translation_invariant_const
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ ξ η : H, AEStronglyMeasurable
      (fun t => inner ℂ η (F t ξ)) volume)
    (htrans : ∀ (s : ℝ) (ξ η : H),
      (fun t => inner ℂ η (F (t + s) ξ)) =ᵐ[volume]
        fun t => inner ℂ η (F t ξ)) :
    ∃ T : H →L[ℂ] H, F =ᵐ[volume] fun _ => T := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hex (i j : ℕ) := aestronglyMeasurable_real_translation_invariant_const
    (fun t => inner ℂ (v i) (F t (v j))) (hF (v j) (v i))
    (fun s => htrans s (v j) (v i))
  choose c hc using hex
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ i j : ℕ,
      inner ℂ (v i) (F t (v j)) = c i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hc i j
  obtain ⟨t₀, ht₀⟩ := hall.exists
  refine ⟨F t₀, hall.mono fun t ht => ?_⟩
  apply ContinuousLinearMap.ext
  have he : (fun ξ => F t ξ) = (fun ξ => F t₀ ξ) := by
    apply hv.equalizer (F t).continuous (F t₀).continuous
    funext j
    exact hv.eq_of_inner_right ℂ (fun i => (ht i j).trans (ht₀ i j).symm)
  exact congrFun he

end

end KadisonKastler

end OAI
