import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.TestBochner

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile128
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [ProperSpace X] in
lemma IsLaplacian.add (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v B) :
    IsLaplacian m (fun x => u x+v x) (fun x => A x+B x) := by
  refine ⟨hu.1.add hfin hv.1,hu.2.1.add hv.2.1,?_⟩
  intro w hw
  have h1 := hu.2.2 w hw
  have h2 := hv.2.2 w hw
  have he := integral_congr_ae (gamma_add_left hfin hpar hu.1.2.1 hv.1.2.1 hw.2.1)
  rw [integral_add (integrable_gamma hfin hu.1 hw) (integrable_gamma hfin hv.1 hw)] at he
  rw [he]
  have hr : (∫ x,(A x+B x)*w x ∂m) = (∫ x,A x*w x ∂m)+(∫ x,B x*w x ∂m) := by
    simp_rw [add_mul]
    exact integral_add (hu.2.1.integrable_mul hw.1) (hv.2.1.integrable_mul hw.1)
  rw [hr]
  linarith

lemma IsTestFunction.add (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v : X → ℝ} (hu : IsTestFunction m u) (hv : IsTestFunction m v) :
    IsTestFunction m (fun x => u x+v x) := by
  have hgen := (laplacian_isLaplacian hu.1).add hfin hpar (laplacian_isLaplacian hv.1)
  obtain ⟨B,hB⟩ := hu.2.1
  obtain ⟨C,hC⟩ := hv.2.1
  obtain ⟨L,hL⟩ := hu.2.2.1
  obtain ⟨M,hM⟩ := hv.2.2.1
  refine ⟨⟨_,hgen⟩,⟨B+C,fun x => (abs_add_le _ _).trans (add_le_add (hB x) (hC x))⟩,
    ⟨L+M,hL.add hM⟩,?_⟩
  exact (sobolev_congr_ae (hgen.ae_laplacian hfin)).mpr (hu.2.2.2.add hfin hv.2.2.2)

variable [SigmaFinite m]

lemma RCD.test_gamma_sobolev {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {u v : X → ℝ} (hu : IsTestFunction m u) (hv : IsTestFunction m v) :
    Sobolev m (gamma m u v) := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hsquare {f : X → ℝ} (hf : IsTestFunction m f) : Sobolev m (gamma m f f) :=
    (sobolev_congr_ae (gamma_self (m := m) f)).mpr (hrcd.test_gradientSquare_sobolev hN hfull hfin o hf)
  have huS := (laplacian_isLaplacian hu.1).1
  have hvS := (laplacian_isLaplacian hv.1).1
  have He : (fun x => (2:ℝ)⁻¹*(gamma m (fun y => u y+v y) (fun y => u y+v y) x-gamma m u u x-gamma m v v x)) =ᵐ[m] gamma m u v := by
    filter_upwards [gamma_add_left hfin hpar huS.2.1 hvS.2.1 ((huS.add hfin hvS).2.1),
      gamma_add_right hfin hpar huS.2.1 huS.2.1 hvS.2.1,
      gamma_add_right hfin hpar hvS.2.1 huS.2.1 hvS.2.1,gamma_comm (m := m) v u] with x h1 h2 h3 h4
    rw [h1,h2,h3,h4]
    ring
  exact (sobolev_congr_ae He).mp (((hsquare (hu.add hfin hpar hv)).sub hfin (hsquare hu)).sub hfin (hsquare hv) |>.const_mul (2:ℝ)⁻¹)
end WeakHessian

end
end InlinedFile128

end OAI
