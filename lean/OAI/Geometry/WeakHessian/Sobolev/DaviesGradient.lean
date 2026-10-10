import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ExpMulLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.davies_gradient (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) :
    (∫ x, (weakGradient m u x)^2 * Real.exp (2*V x) ∂m) ≤
      -2*(∫ x, A x * u x * Real.exp (2*V x) ∂m)+
        4*(L:ℝ)^2*(∫ x, (u x)^2 * Real.exp (2*V x) ∂m) := by
  have hV2 : LipschitzWith (‖(2:ℝ)‖₊*L) (fun x => 2*V x) := (lipschitzWith_smul (2:ℝ)).comp hV
  have hB2 : ∀ᵐ x ∂m, 2*V x ≤ 2*B := hB.mono (fun x hx => by linarith)
  have hv := hu.1.mul_exp hfinite hV2 hB2
  have hexp : AEStronglyMeasurable (fun x => Real.exp (V x)) m :=
    Real.continuous_exp.comp_aestronglyMeasurable hV.continuous.aestronglyMeasurable
  have hexpB : ∀ᵐ x ∂m, |Real.exp (V x)| ≤ Real.exp B :=
    hB.mono (fun x hx => by simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx)
  have hi : Integrable (fun x => (u x)^2*Real.exp (2*V x)) m := by
    apply (memLp_mul_bounded hu.1.1 hexp hexpB).integrable_sq.congr
    exact ae_of_all _ (fun x => by simp only [mul_pow,sq_exp_eq])
  have hDi : Integrable (fun x => (weakGradient m u x)^2*Real.exp (2*V x)) m := by
    apply (memLp_mul_bounded hu.1.2.2 hexp hexpB).integrable_sq.congr
    exact ae_of_all _ (fun x => by simp only [mul_pow,sq_exp_eq])
  have hlap := hu.2.2 (fun x => u x*Real.exp (2*V x)) hv
  have hg : gamma m u (fun x => u x*Real.exp (2*V x)) =ᵐ[m]
      (fun x => Real.exp (2*V x)*((weakGradient m u x)^2+2*u x*gamma m V u x)) := by
    filter_upwards [gamma_comm (m := m) u (fun x => u x*Real.exp (2*V x)),
      gamma_mul_exp_left hfinite hpar hu.1.2.1 (localSobolev_of_lipschitz hfinite hV2)
        hu.1.2.1 hB2 (weakGradient_le_lipschitz hfinite hV2),gamma_self (m := m) u,
      gamma_const_mul_left hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.1.2.1 2]
      with x hc hm hs hc2
    rw [hc,hm,hs,hc2]; ring
  have hb : ∀ᵐ x ∂m, (weakGradient m u x)^2*Real.exp (2*V x) ≤
      2*gamma m u (fun x => u x*Real.exp (2*V x)) x+4*(L:ℝ)^2*((u x)^2*Real.exp (2*V x)) := by
    filter_upwards [hg,abs_gamma_le hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.1.2.1,
      weakGradient_le_lipschitz hfinite hV,weakGradient_nonneg (m := m) u] with x hx hgam hLip hD
    have hgL : |gamma m V u x| ≤ (L:ℝ)*weakGradient m u x :=
      hgam.trans (mul_le_mul_of_nonneg_right hLip hD)
    have hm : |u x*gamma m V u x| ≤ |u x| *(L:ℝ)*weakGradient m u x := by
      rw [abs_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left hgL (abs_nonneg _)
    have hp : (weakGradient m u x)^2 ≤
        2*((weakGradient m u x)^2+2*u x*gamma m V u x)+4*(L:ℝ)^2*(u x)^2 := by
      have hlo := (abs_le.mp hm).1
      nlinarith [sq_nonneg (weakGradient m u x-2*(L:ℝ)*|u x|),sq_abs (u x)]
    rw [hx]
    have HH := mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*V x)).le
    nlinarith [HH]
  have HI := integral_mono_ae hDi (((integrable_gamma hfinite hu.1 hv).const_mul 2).add (hi.const_mul _)) hb
  simp only [Pi.add_apply] at HI
  rw [integral_add ((integrable_gamma hfinite hu.1 hv).const_mul 2) (hi.const_mul _),
    integral_const_mul,integral_const_mul,hlap] at HI
  have he : (∫ x, A x*u x*Real.exp (2*V x) ∂m) =
      ∫ x, A x*(u x*Real.exp (2*V x)) ∂m := by
    apply integral_congr_ae; exact ae_of_all _ (fun x => mul_assoc _ _ _)
  rw [he]; linarith

end WeakHessian

end
end InlinedFile0

end OAI
