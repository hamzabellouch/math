import OAI.Analysis.LipschitzHilbert.Fourier.VerticalDifferenceEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSamplingCommutator
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalKernelMoment

namespace OAI

/-! A quantitative bin/sampling commutator bound from the second absolute
kernel moment and the vertical derivative energy. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingCommutator_energy (K : ℝ → ℂ) (hKm : Measurable K)
    (hK : Integrable K) (hK2 : Integrable (fun s => s^2*‖K s‖))
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (t : ℝ) (ht : |t|≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (verticalSamplingCommutator K u t f) 2 planeMeasure ∧
      (∫ z, ‖verticalSamplingCommutator K u t f z‖^2 ∂planeMeasure)≤
        16*t^2*(∫ s, ‖K s‖)*(∫ s, s^2*‖K s‖)*
          (∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure) := by
  let D := fun p : ℝ×(ℝ×ℝ) => verticalSamplingDifference f u t p.1 p.2
  let E := ∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure
  have hE : 0≤E := integral_nonneg (fun _ => sq_nonneg _)
  have hum := hu.continuous.measurable
  have hDm : Measurable D := by
    change Measurable (fun p : ℝ×(ℝ×ℝ) =>
      f (p.2.1-t,p.2.2-p.1-t*u (p.2.1,p.2.2-p.1))-
        f (p.2.1-t,p.2.2-p.1-t*u p.2))
    fun_prop
  have hs (s : ℝ) := verticalSamplingDifference_energy f u hu t s ht
  have hH : Integrable (fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖D p‖^2)
      (volume.prod planeMeasure) := by
    have hm := (hKm.comp measurable_fst).norm.mul (hDm.norm.pow_const 2)
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun s =>
        ((hs s).1.integrable_norm_pow (by decide : 2≠0)).const_mul ‖K s‖
    · apply (hK2.const_mul (16*t^2*E)).mono'
        hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with s
      change ‖∫ z, ‖‖K s‖*‖D (s,z)‖^2‖ ∂planeMeasure‖≤16*t^2*E*(s^2*‖K s‖)
      have hnonneg : 0≤∫ z, ‖‖K s‖*‖D (s,z)‖^2‖ ∂planeMeasure := integral_nonneg (fun _ => norm_nonneg _)
      rw [Real.norm_of_nonneg hnonneg]
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K s)),Real.norm_of_nonneg (sq_nonneg _)]
      rw [integral_const_mul]
      have hb := mul_le_mul_of_nonneg_left (hs s).2 (norm_nonneg (K s))
      dsimp [D,E] at hb ⊢
      nlinarith only [hb]
  have hCeq : verticalSamplingCommutator K u t f=
      (fun z => ∫ s, K s*D (s,z)) :=
    funext (verticalSamplingCommutator_eq K hK u hum t f)
  have hCm : Measurable (verticalSamplingCommutator K u t f) := by
    rw [hCeq]
    exact ((hKm.comp measurable_fst).mul hDm).stronglyMeasurable.prod_swap.integral_prod_right'.measurable
  have hp : ∀ᵐ z ∂planeMeasure, ‖verticalSamplingCommutator K u t f z‖^2≤
      (∫ s, ‖K s‖)*∫ s, ‖K s‖*‖D (s,z)‖^2 := by
    filter_upwards [hH.prod_left_ae] with z hz
    have hd : Measurable (fun s => ‖D (s,z)‖) := hDm.norm.comp (by fun_prop)
    obtain ⟨hprod,hcs⟩ := weighted_integral_cauchySchwarz volume
      (fun s => ‖K s‖) (fun s => ‖D (s,z)‖) hKm.norm hd
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hK.norm hz
    have hn : ‖verticalSamplingCommutator K u t f z‖≤∫ s, ‖K s‖*‖D (s,z)‖ := by
      rw [hCeq]
      exact norm_integral_le_of_norm_le hprod (Filter.Eventually.of_forall fun s => le_of_eq (norm_mul _ _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  have hdom := hH.integral_prod_right.const_mul (∫ s, ‖K s‖)
  have hi : Integrable (fun z => ‖verticalSamplingCommutator K u t f z‖^2) planeMeasure :=
    hdom.mono' (hCm.norm.pow_const 2).aestronglyMeasurable (by
      filter_upwards [hp] with z hz
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz)
  refine ⟨(memLp_two_iff_integrable_sq_norm hCm.aestronglyMeasurable).2 hi,?_⟩
  have htotal : (∫ s, ∫ z, ‖K s‖*‖D (s,z)‖^2 ∂planeMeasure)≤
      16*t^2*E*(∫ s, s^2*‖K s‖) := by
    rw [←integral_const_mul]
    apply integral_mono hH.integral_prod_left (hK2.const_mul _)
    intro s
    change (∫ z, ‖K s‖*‖D (s,z)‖^2 ∂planeMeasure)≤16*t^2*E*(s^2*‖K s‖)
    rw [integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (hs s).2 (norm_nonneg (K s))
    dsimp [D,E] at hb ⊢
    nlinarith only [hb]
  calc
    _ ≤ ∫ z, (∫ s, ‖K s‖)*(∫ s, ‖K s‖*‖D (s,z)‖^2) ∂planeMeasure :=
      integral_mono_ae hi hdom hp
    _ = (∫ s, ‖K s‖)*(∫ s, ∫ z, ‖K s‖*‖D (s,z)‖^2 ∂planeMeasure) := by
      rw [integral_const_mul]
      exact congrArg (fun a => (∫ s, ‖K s‖)*a)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (s : ℝ) => ‖K s‖*‖D (s,z)‖^2) hH.swap)
    _ ≤ (∫ s, ‖K s‖)*(16*t^2*E*(∫ s, s^2*‖K s‖)) :=
      mul_le_mul_of_nonneg_left htotal (integral_nonneg (fun _ => norm_nonneg _))
    _ = _ := by dsimp only [E]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
