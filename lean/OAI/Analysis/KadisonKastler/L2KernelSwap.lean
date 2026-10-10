import OAI.Analysis.KadisonKastler.L2TensorCoordinates
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Kernel formulas for the L2 Fubini isometry

Testing against scalar tensors identifies the swap of any integrable
kernel represented by its rows and columns. The application uses bounded
phase and indicator kernels multiplied by two L2 vectors.
-/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem inner_scalarLpTensor_kernel (μ : Measure X) (ν : Measure Y)
    (K : X → Y → ℂ) (F : Lp (Lp ℂ 2 ν) 2 μ)
    (hF : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, F x y = K x y)
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    inner ℂ (scalarLpTensor μ f g) F =
      ∫ x, ∫ y, star (f x) * star (g y) * K x y ∂ν ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarLpTensor_apply_ae μ f g, hF] with x hx hrow
  rw [hx, inner_smul_left, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hrow] with y hy
  rw [hy]
  simp only [RCLike.inner_apply]
  change star (f x) * (K x y * star (g y)) = _
  ring

theorem l2ScalarSwap_of_kernel (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : X → Y → ℂ) (F : Lp (Lp ℂ 2 ν) 2 μ) (G : Lp (Lp ℂ 2 μ) 2 ν)
    (hF : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, F x y = K x y)
    (hG : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, G y x = K x y)
    (hint : ∀ (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν),
      Integrable (fun p : X × Y => star (f p.1) * star (g p.2) * K p.1 p.2) (μ.prod ν)) :
    l2ScalarSwap μ ν F = G := by
  apply ext_inner_left ℂ
  intro z
  refine (l2TensorEmbedding_dense ν).induction_on
    (p := fun z => inner ℂ z (l2ScalarSwap μ ν F) = inner ℂ z G) z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro z
    induction z using TensorProduct.inductionOn with
    | tmul g f =>
        change inner ℂ (scalarLpTensor ν g f) (l2ScalarSwap μ ν F) =
          inner ℂ (scalarLpTensor ν g f) G
        have hs := (l2ScalarSwap μ ν).inner_map_map (scalarLpTensor μ f g) F
        rw [l2ScalarSwap_tensor] at hs
        rw [hs,
          inner_scalarLpTensor_kernel μ ν K F hF,
          inner_scalarLpTensor_kernel ν μ (fun y x => K x y) G hG,
          integral_integral_swap (hint f g)]
        apply integral_congr_ae
        filter_upwards [] with y
        apply integral_congr_ae
        filter_upwards [] with x
        ring
    | add z w hz hw =>
        simpa only [map_add, inner_add_left] using congrArg₂ (· + ·) hz hw

theorem integrable_bounded_L2_kernel (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (k : X × Y → ℂ) (hk : Measurable k) (hbound : ∀ p, ‖k p‖ ≤ 1)
    (f f' : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    Integrable (fun p : X × Y =>
      star (f' p.1) * star (g' p.2) * (k p * f p.1 * g p.2)) (μ.prod ν) := by
  have hx := (Lp.memLp f').norm.integrable_mul (Lp.memLp f).norm
  have hy := (Lp.memLp g').norm.integrable_mul (Lp.memLp g).norm
  apply (hx.mul_prod hy).mono'
    (((Lp.stronglyMeasurable f').star.measurable.comp measurable_fst).aestronglyMeasurable.mul
      ((Lp.stronglyMeasurable g').star.measurable.comp measurable_snd).aestronglyMeasurable |>.mul
      ((hk.mul ((Lp.stronglyMeasurable f).measurable.comp measurable_fst)).mul
        ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)).aestronglyMeasurable)
  filter_upwards [] with p
  change ‖star (f' p.1) * star (g' p.2) * (k p * f p.1 * g p.2)‖ ≤
    (‖f' p.1‖ * ‖f p.1‖) * (‖g' p.2‖ * ‖g p.2‖)
  simp only [norm_mul, norm_star]
  calc
    _ ≤ ‖f' p.1‖ * ‖g' p.2‖ * (1 * ‖f p.1‖ * ‖g p.2‖) := by gcongr; exact hbound p
    _ = _ := by ring

end

end KadisonKastler

end OAI
