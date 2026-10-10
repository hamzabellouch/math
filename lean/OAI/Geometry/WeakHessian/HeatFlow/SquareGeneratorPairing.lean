import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TestProduct

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile132
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma IsLaplacian.square_pairing (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v B)
    {L : ℝ≥0} (hL : LipschitzWith L u) {C D : ℝ}
    (huB : ∀ x,|u x| ≤ C) (hvB : ∀ᵐ x ∂m,|v x| ≤ D) :
    2*(∫ x,u x*A x*v x ∂m)-(∫ x,(u x)^2*B x ∂m) =
      -2*(∫ x,v x*(weakGradient m u x)^2 ∂m) := by
  have hsq := hu.mul_lipschitz hfin hpar hu hL hL huB huB
  have h1 := hsq.2.2 v hv.1
  have h2 := hv.2.2 (fun x=>u x*u x) hsq.1
  have hcomm : (∫ x,gamma m (fun y=>u y*u y) v x ∂m) = ∫ x,gamma m v (fun y=>u y*u y) x ∂m :=
    integral_congr_ae (gamma_comm _ _)
  have he : (∫ x,(A x*u x+A x*u x+2*gamma m u u x)*v x ∂m) = ∫ x,(u x)^2*B x ∂m := by
    calc
      _ = -(∫ x,gamma m (fun y=>u y*u y) v x ∂m) := by exact (neg_eq_iff_eq_neg.mp h1.symm)
      _ = -(∫ x,gamma m v (fun y=>u y*u y) x ∂m) := by rw [hcomm]
      _ = ∫ x,(u x)^2*B x ∂m := by
        rw [h2,neg_neg]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring
  have hia : Integrable (fun x=>A x*u x*v x) m :=
    (memLp_mul_bounded hu.2.1 hL.continuous.aestronglyMeasurable (ae_of_all _ huB)).integrable_mul hv.1.1
  have hig := integrable_bounded_weakGradient_sq hu.1 hv.1.1.aestronglyMeasurable hvB
  have he2 : (∫ x,(A x*u x+A x*u x+2*gamma m u u x)*v x ∂m) =
      2*(∫ x,u x*A x*v x ∂m)+2*(∫ x,v x*(weakGradient m u x)^2 ∂m) := by
    calc
      _ = ∫ x,2*(A x*u x*v x)+2*(v x*(weakGradient m u x)^2) ∂m := by
        apply integral_congr_ae
        filter_upwards [gamma_self (m := m) u] with x hx
        rw [hx]; ring
      _ = 2*(∫ x,A x*u x*v x ∂m)+2*(∫ x,v x*(weakGradient m u x)^2 ∂m) := by
        rw [integral_add (hia.const_mul 2) (hig.const_mul 2), integral_const_mul,integral_const_mul]
      _ = _ := by
        have HH : (∫ x,A x*u x*v x ∂m) = ∫ x,u x*A x*v x ∂m :=
          integral_congr_ae (ae_of_all _ fun x => by ring)
        rw [HH]
  rw [he2] at he
  linarith only [he]
end WeakHessian

end
end InlinedFile132

end OAI
