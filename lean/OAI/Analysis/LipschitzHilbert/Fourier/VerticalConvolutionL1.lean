import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinKernel
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! Vertical convolution acts on actual measurable planar functions.
Its L1 and uniform bounds are independent of bin width and carrier. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def verticalTranslation (t : ℝ) : (ℝ×ℝ) ≃ᵐ (ℝ×ℝ) where
  toFun z := (z.1,z.2-t)
  invFun z := (z.1,z.2+t)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.sub measurable_const)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.add measurable_const)

theorem verticalTranslation_measurePreserving (t : ℝ) :
    MeasurePreserving (verticalTranslation t) planeMeasure planeMeasure := by
  change MeasurePreserving (fun z : ℝ×ℝ => (z.1,z.2-t)) _ _
  have hm := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right volume (-t))
  have heq : Prod.map (id : ℝ → ℝ) (fun x => x + -t)=
      (fun z : ℝ×ℝ => (z.1,z.2-t)) := by
    funext z
    cases z
    rfl
  rw [heq] at hm
  exact hm

theorem integral_verticalTranslation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (f : ℝ×ℝ → V) :
    (∫ z, f (z.1,z.2-t) ∂planeMeasure)=∫ z, f z ∂planeMeasure :=
  (verticalTranslation_measurePreserving t).integral_comp' f

theorem verticalConvolution_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (fun p : ℝ×(ℝ×ℝ) => K p.1*f (p.2.1,p.2.2-p.1))
      (volume.prod planeMeasure) := by
  have hm : Measurable (fun p : ℝ×(ℝ×ℝ) => K p.1*f (p.2.1,p.2.2-p.1)) := by
    exact (hKm.comp measurable_fst).mul (hfm.comp (by fun_prop))
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((verticalTranslation_measurePreserving t).integrable_comp_of_integrable hf).const_mul (K t)
  · have heq (t : ℝ) : (∫ z, ‖K t*f (z.1,z.2-t)‖ ∂planeMeasure)=
        ‖K t‖*(∫ z, ‖f z‖ ∂planeMeasure) := by
      simp_rw [norm_mul]
      rw [integral_const_mul,integral_verticalTranslation t (fun z => ‖f z‖)]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem verticalConvolution_measurable (K : ℝ → ℂ) (hK : Measurable K)
    (f : ℝ×ℝ → ℂ) (hf : Measurable f) : Measurable (verticalConvolution K f) := by
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ => K p.2*f (p.1.1,p.1.2-p.2)) := by
    exact (hK.comp measurable_snd).mul (hf.comp (by fun_prop))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem verticalConvolution_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (verticalConvolution K f) planeMeasure :=
  (verticalConvolution_joint_integrable K hK hKm f hfm hf).integral_prod_right

theorem verticalConvolution_l1_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    (∫ z, ‖verticalConvolution K f z‖ ∂planeMeasure)≤
      (∫ t, ‖K t‖)*(∫ z, ‖f z‖ ∂planeMeasure) := by
  have hi := verticalConvolution_joint_integrable K hK hKm f hfm hf
  calc
    _ ≤ ∫ z, ∫ t, ‖K t*f (z.1,z.2-t)‖ ∂volume ∂planeMeasure := by
      apply integral_mono (verticalConvolution_integrable K hK hKm f hfm hf).norm
        hi.norm.integral_prod_right
      exact fun z => norm_integral_le_integral_norm _
    _ = ∫ t, ∫ z, ‖K t*f (z.1,z.2-t)‖ ∂planeMeasure ∂volume :=
      integral_integral_swap hi.norm.swap
    _ = _ := by
      simp_rw [norm_mul,integral_const_mul,integral_verticalTranslation _ (fun z => ‖f z‖)]
      rw [integral_mul_const]

theorem verticalConvolution_horizontal_support (K : ℝ → ℂ) (f : ℝ×ℝ → ℂ)
    (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → verticalConvolution K f z=0 := by
  intro z hz
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun t => by
    change K t*f (z.1,z.2-t)=0
    rw [hf (z.1,z.2-t) hz,mul_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
