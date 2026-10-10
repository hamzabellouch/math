import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-! The continuous packet identity in §2, with the actual convolution
kernels and the exact area normalization. Absolute integrability follows
from L1 kernels and input and a bounded measurable test. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

abbrev planeMeasure : Measure (ℝ × ℝ) := volume.prod volume

def kernelConvolution (K f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  convolution f K (ContinuousLinearMap.mul ℝ ℂ) planeMeasure

def analyzingWave (area : ℝ) (K : ℝ × ℝ → ℂ) (z y : ℝ × ℝ) : ℂ :=
  (area : ℂ) * conj (K (z-y))

def synthesisWave (area : ℝ) (K : ℝ × ℝ → ℂ) (z x : ℝ × ℝ) : ℂ :=
  (area : ℂ) * K (x-z)

def coefficient (f : ℝ × ℝ → ℂ) (area : ℝ) (K : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  ∫ y, f y * conj (analyzingWave area K z y) ∂planeMeasure

theorem coefficient_eq (f K : ℝ × ℝ → ℂ) (area : ℝ) (z : ℝ × ℝ) :
    coefficient f area K z = (area : ℂ) * kernelConvolution K f z := by
  unfold coefficient analyzingWave kernelConvolution convolution
  simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply, ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem kernelConvolution_integrable {K f : ℝ × ℝ → ℂ}
    (hK : Integrable K planeMeasure) (hf : Integrable f planeMeasure) :
    Integrable (kernelConvolution K f) planeMeasure :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℂ) hK

theorem weighted_convolution_integrable (K c b g : ℝ × ℝ → ℂ)
    (hK : Integrable K planeMeasure) (hc : Integrable c planeMeasure)
    (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖≤Mb) (hgb : ∀ x, ‖g x‖≤Mg) :
    Integrable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (c p.2*K (p.1-p.2))*(b p.1*conj (g p.1))) (planeMeasure.prod planeMeasure) := by
  apply (hc.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hK).mul_bdd (c := Mb*Mg)
  · exact ((hb.comp measurable_fst).mul
      (Complex.continuous_conj.measurable.comp (hg.comp measurable_fst))).aestronglyMeasurable
  · filter_upwards [] with p
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hbb p.1) (hgb p.1) (norm_nonneg _) ((norm_nonneg _).trans (hbb p.1))

def packetProduct (KA KB f b g : ℝ × ℝ → ℂ) (area : ℝ) (z : ℝ × ℝ) : ℂ :=
  coefficient f area KB z *
    ∫ x, b x * synthesisWave area KA z x * conj (g x) ∂planeMeasure

theorem packetProduct_eq (KA KB f b g : ℝ × ℝ → ℂ) (area : ℝ) (z : ℝ × ℝ) :
    packetProduct KA KB f b g area z = (area : ℂ)^2 * ∫ x,
      (kernelConvolution KB f z*KA (x-z))*(b x*conj (g x)) ∂planeMeasure := by
  rw [packetProduct, coefficient_eq]
  unfold synthesisWave
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem packetProduct_integrable (KA KB f b g : ℝ × ℝ → ℂ)
    (hA : Integrable KA planeMeasure) (hB : Integrable KB planeMeasure)
    (hf : Integrable f planeMeasure) (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖≤Mb) (hgb : ∀ x, ‖g x‖≤Mg) (area : ℝ) :
    Integrable (packetProduct KA KB f b g area) planeMeasure := by
  have h := weighted_convolution_integrable KA (kernelConvolution KB f) b g hA
    (kernelConvolution_integrable hB hf) hb hg Mb Mg hbb hgb
  apply (h.integral_prod_right.const_mul ((area:ℂ)^2)).congr
  filter_upwards [] with z
  exact (packetProduct_eq KA KB f b g area z).symm

theorem continuous_packet_identity (KA KB f b g : ℝ × ℝ → ℂ)
    (hA : Integrable KA planeMeasure) (hB : Integrable KB planeMeasure)
    (hf : Integrable f planeMeasure) (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖ ≤ Mb) (hgb : ∀ x, ‖g x‖ ≤ Mg)
    (area : ℝ) (ha : area ≠ 0) :
    (∫ x, b x * kernelConvolution KA (kernelConvolution KB f) x * conj (g x) ∂planeMeasure) =
      ((area : ℂ)^2)⁻¹ * ∫ z, coefficient f area KB z *
        (∫ x, b x * synthesisWave area KA z x * conj (g x) ∂planeMeasure) ∂planeMeasure := by
  let c := kernelConvolution KB f
  let H := fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
    (c p.2 * KA (p.1-p.2)) * (b p.1 * conj (g p.1))
  have hc : Integrable c planeMeasure := kernelConvolution_integrable hB hf
  have hH : Integrable H (planeMeasure.prod planeMeasure) :=
    weighted_convolution_integrable KA c b g hA hc hb hg Mb Mg hbb hgb
  have hleft (x : ℝ × ℝ) :
      b x * kernelConvolution KA c x * conj (g x) = ∫ z, H (x,z) ∂planeMeasure := by
    change b x * (∫ z, c z * KA (x-z) ∂planeMeasure) * conj (g x) = _
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [H]
    ring
  have hright (z : ℝ × ℝ) :
      coefficient f area KB z *
        (∫ x, b x * synthesisWave area KA z x * conj (g x) ∂planeMeasure) =
      (area : ℂ)^2 * ∫ x, H (x,z) ∂planeMeasure := by
    rw [coefficient_eq]
    unfold synthesisWave
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [H]
    ring
  have hsum : (∫ z, coefficient f area KB z *
        (∫ x, b x * synthesisWave area KA z x * conj (g x) ∂planeMeasure) ∂planeMeasure) =
      (area : ℂ)^2 * ∫ z, ∫ x, H (x,z) ∂planeMeasure ∂planeMeasure := by
    calc
      _ = ∫ z, (area : ℂ)^2 * ∫ x, H (x,z) ∂planeMeasure ∂planeMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall hright)
      _ = _ := integral_const_mul _ _
  calc
    _ = ∫ x, ∫ z, H (x,z) ∂planeMeasure ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ z, ∫ x, H (x,z) ∂planeMeasure ∂planeMeasure := integral_integral_swap hH
    _ = _ := by
      rw [hsum]
      have ha' : (area : ℂ) ≠ 0 := by exact_mod_cast ha
      field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
