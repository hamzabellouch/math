import Mathlib
import OAI.Geometry.WeakHessian.Calculus.GammaLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile27
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma weighted_gamma_bound (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {a u φ W : X → ℝ}
    (ha : AEStronglyMeasurable a m) (hu : Sobolev m u) (hφ : LocalSobolev m φ)
    (hW : ∀ᵐ x ∂m, 0 ≤ W x) (hD : ∀ᵐ x ∂m, weakGradient m φ x ≤ W x)
    (hAW : MemLp (fun x => a x*W x) 2 m) :
    Integrable (fun x => a x*gamma m u φ x) m ∧
      |∫ x,a x*gamma m u φ x ∂m| ≤
        ‖hAW.toLp (fun x => a x*W x)‖*‖hu.2.2.toLp (weakGradient m u)‖ := by
  have hB : ∀ᵐ x ∂m, ‖a x*gamma m u φ x‖ ≤ ‖a x*W x‖*weakGradient m u x := by
    filter_upwards [abs_gamma_le hfin hpar hu.2.1 hφ,hW,hD,
      weakGradient_nonneg (m := m) u] with x hx hw hd hn
    have H := hx.trans (mul_le_mul_of_nonneg_left hd hn)
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hw,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left H (abs_nonneg (a x))
  have hi := hAW.norm.integrable_mul hu.2.2
  have hme : AEStronglyMeasurable (fun x => a x*gamma m u φ x) m :=
    ha.mul (gamma_aestronglyMeasurable hfin hu.2.1 hφ)
  have hi' := hi.mono' hme hB
  refine ⟨hi',?_⟩
  have H : |∫ x,a x*gamma m u φ x ∂m| ≤ ∫ x, ‖a x*W x‖*weakGradient m u x ∂m := by
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans (integral_mono_ae hi'.norm hi hB)
  have J := abs_integral_mul_le_L2_norm hAW.norm hu.2.2
  have hn : ‖hAW.norm.toLp (fun x => ‖a x*W x‖)‖ = ‖hAW.toLp (fun x => a x*W x)‖ := by
    simp only [Lp.norm_toLp,eLpNorm_norm _ hAW.aestronglyMeasurable]
  rw [hn] at J
  exact H.trans ((le_abs_self _).trans J)

lemma weighted_gamma_root_difference (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v φ W : X → ℝ}
    (hu : Sobolev m u) (hv : Sobolev m v) (hφ : LocalSobolev m φ)
    (hW : ∀ᵐ x ∂m, 0 ≤ W x) (hD : ∀ᵐ x ∂m, weakGradient m φ x ≤ W x)
    (huW : MemLp (fun x => u x*W x) 2 m) (hvW : MemLp (fun x => v x*W x) 2 m)
    (hdW : MemLp (fun x => (u x-v x)*W x) 2 m) :
    |(∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m)| ≤
      ‖hdW.toLp (fun x => (u x-v x)*W x)‖*‖hu.2.2.toLp (weakGradient m u)‖+
      ‖hvW.toLp (fun x => v x*W x)‖*‖(hu.sub hfin hv).2.2.toLp (weakGradient m (fun x => u x-v x))‖ := by
  let hsub := hu.sub hfin hv
  have h1 := weighted_gamma_bound hfin hpar hu.1.aestronglyMeasurable hu hφ hW hD huW
  have h2 := weighted_gamma_bound hfin hpar hv.1.aestronglyMeasurable hv hφ hW hD hvW
  have h3 := weighted_gamma_bound (a := fun x => u x-v x) hfin hpar
    (hu.1.aestronglyMeasurable.sub hv.1.aestronglyMeasurable) hu hφ hW hD hdW
  have h4 := weighted_gamma_bound hfin hpar hv.1.aestronglyMeasurable hsub hφ hW hD hvW
  have he : (∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m) =
      (∫ x,(u x-v x)*gamma m u φ x ∂m)+(∫ x,v x*gamma m (fun y => u y-v y) φ x ∂m) := by
    rw [← integral_sub h1.1 h2.1,← integral_add h3.1 h4.1]
    apply integral_congr_ae
    filter_upwards [gamma_sub_left hfin hpar hu.2.1 hv.2.1 hφ] with x hx
    rw [hx]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h3.2 h4.2)
end WeakHessian

end
end InlinedFile27

end OAI
