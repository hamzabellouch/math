import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteCubeQuadrature
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

/-! The recursive quadrature integral is the actual product Lebesgue
integral on the cube. This identifies the six-coordinate computation with
the finite Coulomb box, rather than a separately defined integral. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.UniformQuadrature

def cubeMeasure (a b : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc a b))

instance cubeMeasure_finite (a b : ℝ) (n : ℕ) : IsFiniteMeasure (cubeMeasure a b n) := by
  unfold cubeMeasure
  infer_instance

theorem cubeIntegral_eq_integral (n : ℕ) {a b : ℝ} (hab : a ≤ b)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f (cubeMeasure a b n)) :
    cubeIntegral a b n f = ∫ x, f x ∂cubeMeasure a b n := by
  induction n with
  | zero =>
    have he : f = fun _ => f Fin.elim0 := funext (fun x => congrArg f (Subsingleton.elim x _))
    rw [he]
    simp [cubeIntegral, cubeMeasure, Measure.pi_empty_univ, measureReal_def]
  | succ n ih =>
    let μ : Measure ℝ := volume.restrict (Set.Icc a b)
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
        (μ.prod (cubeMeasure a b n)) := by
      have ht := (hp.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurableEmbedding).mpr hf
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero', cubeMeasure, μ] using ht
    have hsplit : (∫ x, f x ∂cubeMeasure a b (n + 1)) =
        ∫ x, ∫ v, f (Fin.cons x v) ∂cubeMeasure a b n ∂μ := by
      change (∫ x, f x ∂Measure.pi (fun _ : Fin (n + 1) => μ)) = _
      rw [← hp.integral_comp']
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero', cubeMeasure, μ] using integral_prod _ hprod
    rw [hsplit]
    change (∫ x in a..b, cubeIntegral a b n (fun v => f (Fin.cons x v))) = _
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [hprod.prod_right_ae] with x hx
    exact ih hx

end ContinuumCoulomb.UniformQuadrature

end

end OAI
