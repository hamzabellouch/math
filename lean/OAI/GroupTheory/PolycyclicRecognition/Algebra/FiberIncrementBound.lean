import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.LIntegral

namespace OAI

/-! # Comparing whole fibers by bounded increments

Tonelli and the left-Haar change of variables turn a two-region oscillation
integral into a bounded-parameter integral of the original increment errors.
The translating center may depend on the section point.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PolycyclicRecognition

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  [MeasurableInv G] [MeasurableSpace X]

omit [MeasurableInv G] in
/-- Enlarge a translated averaging region using its actual inclusion.
The integrand needs no regularity for this step. -/
theorem lintegral_translate_le (m : Measure G) [m.IsMulLeftInvariant]
    (f : G → ℝ≥0∞) (q : G) {B C : Set G} (h : ∀ x ∈ B, q * x ∈ C) :
    (∫⁻ x in B, f (q * x) ∂m) ≤ ∫⁻ x in C, f x ∂m := by
  rw [(measurePreserving_mul_left m q).setLIntegral_comp_emb
    (MeasurableEquiv.mulLeft q).measurableEmbedding f B]
  exact lintegral_mono_set (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

/-- The substitution `t = x₂⁻¹x₁` bounds whole-region oscillations by
increments whose parameters lie in one fixed set. -/
theorem fiber_increment_lintegral_le
    (ν : Measure X) [SFinite ν] (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    {B C T : Set G} (hB : MeasurableSet B)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (f : X → G → G → ℝ≥0∞) (hf : Measurable (fun q : X × G × G => f q.1 q.2.1 q.2.2)) :
    (∫⁻ p, ∫⁻ x₁ in C, ∫⁻ x₂ in B, f p x₂ (x₂⁻¹ * x₁) ∂m ∂m ∂ν) ≤
      ∫⁻ t in T, ∫⁻ p, ∫⁻ x₂ in B, f p x₂ t ∂m ∂ν ∂m := by
  have hp (p : X) : Measurable (fun q : G × G => f p q.1 q.2) :=
    hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  calc
    _ = ∫⁻ p, ∫⁻ x₂ in B, ∫⁻ x₁ in C, f p x₂ (x₂⁻¹ * x₁) ∂m ∂m ∂ν := by
      apply lintegral_congr
      intro p
      exact lintegral_lintegral_swap ((hp p).comp
        (measurable_snd.prodMk (measurable_snd.inv.mul measurable_fst))).aemeasurable
    _ ≤ ∫⁻ p, ∫⁻ x₂ in B, ∫⁻ t in T, f p x₂ t ∂m ∂m ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with x₂ hx₂
      have heq : (∫⁻ x₁ in C, f p x₂ (x₂⁻¹ * x₁) ∂m) =
          ∫⁻ t in (fun t => x₂ * t) ⁻¹' C, f p x₂ t ∂m := by
        have h := (measurePreserving_mul_left m x₂).setLIntegral_comp_preimage_emb
          (MeasurableEquiv.mulLeft x₂).measurableEmbedding
          (fun x₁ => f p x₂ (x₂⁻¹ * x₁)) C
        simpa only [inv_mul_cancel_left] using h.symm
      rw [heq]
      apply lintegral_mono_set
      intro t ht
      have h := hT x₂ hx₂ (x₂ * t) ht
      simpa only [inv_mul_cancel_left] using h
    _ = ∫⁻ p, ∫⁻ t in T, ∫⁻ x₂ in B, f p x₂ t ∂m ∂m ∂ν := by
      apply lintegral_congr
      intro p
      exact lintegral_lintegral_swap (hp p).aemeasurable
    _ = _ := by
      apply lintegral_lintegral_swap
      have hm : Measurable (fun q : (X × G) × G => f q.1.1 q.2 q.1.2) :=
        hf.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
      exact (hm.lintegral_prod_right' (ν := m.restrict B)).aemeasurable

/-- The two-region estimate remains uniform when the first averaging
region is translated by a center depending on the section point. -/
theorem fiber_translated_increment_lintegral_le
    (ν : Measure X) [SFinite ν] (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    {B C T : Set G} (hB : MeasurableSet B)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (q : X → G) (hC : ∀ p x, x ∈ B → q p * x ∈ C)
    (f : X → G → G → ℝ≥0∞) (hf : Measurable (fun a : X × G × G => f a.1 a.2.1 a.2.2)) :
    (∫⁻ p, ∫⁻ x₁ in B, ∫⁻ x₂ in B, f p x₂ (x₂⁻¹ * (q p * x₁)) ∂m ∂m ∂ν) ≤
      ∫⁻ t in T, ∫⁻ p, ∫⁻ x₂ in B, f p x₂ t ∂m ∂ν ∂m := by
  refine le_trans (lintegral_mono fun p => ?_)
    (fiber_increment_lintegral_le ν m hB hT f hf)
  exact lintegral_translate_le m
    (fun x₁ => ∫⁻ x₂ in B, f p x₂ (x₂⁻¹ * x₁) ∂m) (q p) (hC p)

/-- Uniform control on the compact increment region bounds the whole
oscillation integral by the Haar mass of that region. -/
theorem fiber_translated_increment_uniform_le
    (ν : Measure X) [SFinite ν] (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    {B C T : Set G} (hB : MeasurableSet B) (hTm : MeasurableSet T)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (q : X → G) (hC : ∀ p x, x ∈ B → q p * x ∈ C)
    (f : X → G → G → ℝ≥0∞) (hf : Measurable (fun a : X × G × G => f a.1 a.2.1 a.2.2))
    {c : ℝ≥0∞} (hbound : ∀ t ∈ T, (∫⁻ p, ∫⁻ x₂ in B, f p x₂ t ∂m ∂ν) ≤ c) :
    (∫⁻ p, ∫⁻ x₁ in B, ∫⁻ x₂ in B, f p x₂ (x₂⁻¹ * (q p * x₁)) ∂m ∂m ∂ν) ≤
      c * m T := by
  refine (fiber_translated_increment_lintegral_le ν m hB hT q hC f hf).trans ?_
  calc
    _ ≤ ∫⁻ _t in T, c ∂m := lintegral_mono_ae (by
      filter_upwards [ae_restrict_mem hTm] with t ht using hbound t ht)
    _ = _ := by rw [setLIntegral_const]

end PolycyclicRecognition

end

end OAI
