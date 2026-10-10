import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionL4
import OAI.Analysis.LipschitzHilbert.Fourier.ReflectedBandProjection

namespace OAI

/-! Actual convolution duality for an integrable input and a bounded test. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def reverseLineConvolution (K g : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t, K t*g (x+t)

theorem lineConvolution_pairing (K f g : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hf : Integrable f) (hfm : Measurable f)
    (hgm : Measurable g) (B : ℝ) (hgb : ∀ x, ‖g x‖≤B) :
    (∫ x, lineConvolution K f x*g x)=(∫ x, f x*reverseLineConvolution K g x) := by
  have hbase : Integrable (fun p : ℝ×ℝ => K p.2*f (p.1-p.2)) :=
    hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf
  have hJ : Integrable (fun p : ℝ×ℝ => (K p.2*f (p.1-p.2))*g p.1) := by
    apply (hbase.norm.mul_const B).mono' (by fun_prop)
    filter_upwards [] with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hgb _) (norm_nonneg _)
  have hbase' : Integrable (fun p : ℝ×ℝ => ‖f p.1‖*‖K p.2‖) := hf.norm.mul_prod hK.norm
  have hJ' : Integrable (fun p : ℝ×ℝ => (K p.2*f p.1)*g (p.1+p.2)) := by
    apply (hbase'.mul_const B).mono' (by fun_prop)
    filter_upwards [] with p
    simp only [norm_mul]
    calc
      _ ≤ (‖K p.2‖*‖f p.1‖)*B := mul_le_mul_of_nonneg_left (hgb _) (by positivity)
      _ = _ := by ring
  calc
    _ = ∫ x, ∫ t, (K t*f (x-t))*g x := by simp_rw [lineConvolution,integral_mul_const]
    _ = ∫ t, ∫ x, (K t*f (x-t))*g x := integral_integral_swap hJ
    _ = ∫ t, ∫ y, (K t*f y)*g (y+t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x : ℝ => (K t*f (x-t))*g x) t).symm
    _ = ∫ y, ∫ t, (K t*f y)*g (y+t) := (integral_integral_swap hJ').symm
    _ = _ := by
      have he (y t : ℝ) : (K t*f y)*g (y+t)=f y*(K t*g (y+t)) := by ring
      simp_rw [he,integral_const_mul]
      rfl

theorem reverseLineConvolution_conj (K g : ℝ → ℂ)
    (hodd : ∀ t, K (-t)= -K t) (hreal : ∀ t, conj (K t)=K t) (x : ℝ) :
    reverseLineConvolution K (fun y => conj (g y)) x= -conj (lineConvolution K g x) := by
  unfold reverseLineConvolution lineConvolution
  rw [←integral_neg_eq_self (fun t : ℝ => K t*conj (g (x+t)))]
  simp only [hodd,neg_mul,←sub_eq_add_neg]
  rw [integral_neg,←integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [map_mul,hreal]

end LipschitzHilbert.PacketRepresentation

end

end OAI
