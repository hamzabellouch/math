import OAI.Analysis.KadisonKastler.RegularPacketIntegrals
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Integrability of the packet reconstruction kernel

An integrable weight in the packet variables and a translated `L²`
square give an integrable three-variable majorant. This justifies the
Fubini interchange in the finite packet reconstruction without assuming
bounded representatives of the Hilbert-space vectors.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

private theorem integrable_weighted_translate
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ) (hw : Integrable w μ)
    (k : X → ℝ) (hk : Measurable k)
    (g : ℝ → ℝ) (hg : Integrable g volume) (hgm : StronglyMeasurable g) :
    Integrable (fun p : X × ℝ => w p.1 * g (p.2 + k p.1))
      (μ.prod (volume : Measure ℝ)) := by
  have hm : AEStronglyMeasurable
      (fun p : X × ℝ => w p.1 * g (p.2 + k p.1))
      (μ.prod (volume : Measure ℝ)) :=
    hw.aestronglyMeasurable.comp_fst.mul
      (hgm.comp_measurable (measurable_snd.add (hk.comp measurable_fst))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [Function.comp_def] using
      ((measurePreserving_add_right (volume : Measure ℝ) (k x)).integrable_comp_of_integrable hg).const_mul (w x)
  · have he (x : X) :
        (∫ r : ℝ, ‖w x * g (r + k x)‖) = ‖w x‖ * ∫ r : ℝ, ‖g r‖ := by
      simp only [norm_mul]
      rw [integral_const_mul]
      congr 1
      exact integral_add_right_eq_self (fun r : ℝ => ‖g r‖) (k x)
    simp_rw [he]
    exact hw.norm.mul_const _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
/-- The complete scalar kernel is integrable over the two packet
variables and the translation variable. -/
theorem integrable_regularPacket_kernel
    (φ ψ : ℝ → ℂ) (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    (A : H →L[ℂ] H) (f g : RegularCoreHilbert H) :
    Integrable (fun p : (ℝ × ℝ) × ℝ =>
      (φ p.1.1 * star (ψ p.1.2)) *
        inner ℂ ((U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1)))
          (A ((U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2)))))
      (((volume : Measure ℝ).prod volume).prod volume) := by
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  let w : ℝ × ℝ → ℂ := fun q => φ q.1 * star (ψ q.2)
  have hψs : Integrable (fun t => star (ψ t)) volume := by
    apply hψ.norm.mono' hψ.aestronglyMeasurable.star
    filter_upwards [] with t
    change ‖star (ψ t)‖ ≤ ‖ψ t‖
    exact (norm_star (ψ t)).le
  have hw : Integrable w μ := hφ.mul_prod hψs
  have hfm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      (U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1))) (μ.prod volume) := by
    apply aestronglyMeasurable_field_apply
    · intro ξ
      exact ((hU ξ).comp (continuous_fst.comp continuous_fst)).aestronglyMeasurable
    · exact ((Lp.stronglyMeasurable f).comp_measurable
        (measurable_snd.add (measurable_fst.comp measurable_fst))).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      (U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2))) (μ.prod volume) := by
    apply aestronglyMeasurable_field_apply
    · intro ξ
      exact ((hU ξ).comp (continuous_snd.comp continuous_fst)).aestronglyMeasurable
    · exact ((Lp.stronglyMeasurable g).comp_measurable
        (measurable_snd.add (measurable_snd.comp measurable_fst))).aestronglyMeasurable
  have hf2 : Integrable (fun t : ℝ => ‖f t‖ ^ 2) volume :=
    (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hg2 : Integrable (fun t : ℝ => ‖g t‖ ^ 2) volume :=
    (Lp.memLp g).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hb₁ := integrable_weighted_translate μ (fun q => ‖w q‖ * ‖A‖)
    (hw.norm.mul_const ‖A‖) Prod.fst measurable_fst
    (fun t => ‖f t‖ ^ 2) hf2 ((Lp.stronglyMeasurable f).norm.pow 2)
  have hb₂ := integrable_weighted_translate μ (fun q => ‖w q‖ * ‖A‖)
    (hw.norm.mul_const ‖A‖) Prod.snd measurable_snd
    (fun t => ‖g t‖ ^ 2) hg2 ((Lp.stronglyMeasurable g).norm.pow 2)
  apply (hb₁.add hb₂).mono'
    (hw.aestronglyMeasurable.comp_fst.mul
      (hfm.inner (A.continuous.comp_aestronglyMeasurable hgm)))
  filter_upwards [] with p
  change ‖w p.1 * inner ℂ _ _‖ ≤
    ‖w p.1‖ * ‖A‖ * ‖f (p.2 + p.1.1)‖ ^ 2 +
      ‖w p.1‖ * ‖A‖ * ‖g (p.2 + p.1.2)‖ ^ 2
  rw [norm_mul]
  have hinner : ‖inner ℂ
      ((U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1)))
      (A ((U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2))))‖ ≤
      ‖A‖ * (‖f (p.2 + p.1.1)‖ * ‖g (p.2 + p.1.2)‖) := by
    apply (norm_inner_le_norm _ _).trans
    calc
      _ ≤ ‖(U (Multiplicative.ofAdd p.1.1) : H →L[ℂ] H) (f (p.2 + p.1.1))‖ *
          (‖A‖ * ‖(U (Multiplicative.ofAdd p.1.2) : H →L[ℂ] H) (g (p.2 + p.1.2))‖) :=
        mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = _ := by rw [Unitary.norm_map, Unitary.norm_map]; ring
  have hquad : ‖f (p.2 + p.1.1)‖ * ‖g (p.2 + p.1.2)‖ ≤
      ‖f (p.2 + p.1.1)‖ ^ 2 + ‖g (p.2 + p.1.2)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f (p.2 + p.1.1)‖ - ‖g (p.2 + p.1.2)‖)]
  calc
    _ ≤ ‖w p.1‖ * (‖A‖ * (‖f (p.2 + p.1.1)‖ * ‖g (p.2 + p.1.2)‖)) :=
      mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ ≤ ‖w p.1‖ * (‖A‖ * (‖f (p.2 + p.1.1)‖ ^ 2 + ‖g (p.2 + p.1.2)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hquad (norm_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

end

end KadisonKastler

end OAI
