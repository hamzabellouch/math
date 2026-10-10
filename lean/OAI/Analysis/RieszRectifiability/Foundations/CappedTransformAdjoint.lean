import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedPairingSymmetrization

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter

theorem bounded_kernel_two_measures_bilinear_integrable {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SFinite μ] [SFinite ν] (k : X × X → ℝ) (hk : Measurable k)
    (B : ℝ) (hB : ∀ q, |k q| ≤ B)
    (f g : X → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun q : X × X => f q.1 * g q.2 * k q) (μ.prod ν) := by
  apply ((hf.abs.mul_prod hg.abs).mul_const B).mono'
    (((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul hk).aestronglyMeasurable
  exact Eventually.of_forall fun q => by
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB q) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem scalarCappedTransform_adjoint {d : ℕ} (m : ℕ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [SFinite ν]
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f ν) (hg : Integrable g μ) :
    Integrable (fun x => scalarCappedTransform m ν e ε f x * g x) μ ∧
      Integrable (fun y => f y * scalarCappedTransform m μ e ε g y) ν ∧
      (∫ x, scalarCappedTransform m ν e ε f x * g x ∂μ) =
        -(∫ y, f y * scalarCappedTransform m μ e ε g y ∂ν) := by
  let F : Ambient d × Ambient d → ℝ := fun q => g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
  have hF : Integrable F (μ.prod ν) := bounded_kernel_two_measures_bilinear_integrable μ ν
    (scalarCappedRieszKernel m e ε) (scalarCappedRieszKernel_continuous m e ε hε).measurable
    (‖e‖ * (ε ^ m)⁻¹) (scalarCappedRieszKernel_bound m e ε hε) g f hgm hfm hg hf
  have hleft (x : Ambient d) : (∫ y, F (x, y) ∂ν) =
      scalarCappedTransform m ν e ε f x * g x := by
    calc
      _ = g x * ∫ y, f y * scalarCappedRieszKernel m e ε (x, y) ∂ν := by
        simp only [F, mul_assoc, integral_const_mul]
      _ = _ := by rw [scalarCappedTransform]; ring
  have hright (y : Ambient d) : (∫ x, F (x, y) ∂μ) =
      -(f y * scalarCappedTransform m μ e ε g y) := by
    calc
      _ = ∫ x, -(f y * (g x * scalarCappedRieszKernel m e ε (y, x))) ∂μ := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only [F]
        have hs : scalarCappedRieszKernel m e ε (x, y) =
            -scalarCappedRieszKernel m e ε (y, x) :=
          scalarCappedRieszKernel_swap m e ε (y, x)
        rw [hs]
        ring
      _ = _ := by rw [integral_neg, integral_const_mul]; rfl
  have hLI : Integrable (fun x => scalarCappedTransform m ν e ε f x * g x) μ :=
    hF.integral_prod_left.congr (Eventually.of_forall hleft)
  have hRIneg : Integrable (fun y => -(f y * scalarCappedTransform m μ e ε g y)) ν :=
    hF.integral_prod_right.congr (Eventually.of_forall hright)
  have hRI : Integrable (fun y => f y * scalarCappedTransform m μ e ε g y) ν := by
    have hd : Integrable (fun y => -(-(f y * scalarCappedTransform m μ e ε g y))) ν := hRIneg.neg
    simpa only [neg_neg] using! hd
  refine ⟨hLI, hRI, ?_⟩
  calc
    _ = ∫ q, F q ∂μ.prod ν :=
      ((integral_prod F hF).trans (integral_congr_ae (Eventually.of_forall hleft))).symm
    _ = ∫ y, -(f y * scalarCappedTransform m μ e ε g y) ∂ν :=
      (integral_prod_symm F hF).trans (integral_congr_ae (Eventually.of_forall hright))
    _ = _ := integral_neg _

end

end RieszRectifiability

end OAI
