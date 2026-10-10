import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CompContDiffLipschitz
import OAI.Geometry.WeakHessian.Calculus.GammaLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile120
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.comp_contDiff (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hLip : LipschitzWith L u) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {C D : ℝ≥0} (hC : LipschitzWith C φ) (hD : LipschitzWith D (deriv φ)) (h0 : φ 0 = 0) :
    IsLaplacian m (φ ∘ u) (fun x => deriv φ (u x)*A x+deriv (deriv φ) (u x)*gamma m u u x) := by
  have hc : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hη : LipschitzWith (D*L) (deriv φ ∘ u) := hD.comp hLip
  have hηS := localSobolev_of_lipschitz hfin hη
  have hηB : ∀ᵐ x ∂m,|(deriv φ ∘ u) x| ≤ C := ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hC
  have hηG : ∀ᵐ x ∂m,|weakGradient m (deriv φ ∘ u) x| ≤ (D*L:ℝ≥0) := by
    filter_upwards [weakGradient_nonneg (m := m) (deriv φ ∘ u),weakGradient_le_lipschitz hfin hη] with x hn hb
    simpa only [abs_of_nonneg hn] using hb
  have hη2B : ∀ᵐ x ∂m,|deriv (deriv φ) (u x)| ≤ D := ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hD
  have hη2M := hd.continuous_deriv le_rfl |>.comp hLip.continuous |>.aestronglyMeasurable (μ := m)
  have hterm1 : MemLp (fun x => deriv φ (u x)*A x) 2 m := by
    simpa only [mul_comm,Function.comp_def] using memLp_mul_bounded hu.2.1 hη.continuous.aestronglyMeasurable hηB
  have hterm2 : MemLp (fun x => deriv (deriv φ) (u x)*gamma m u u x) 2 m := by
    simpa only [mul_comm,Function.comp_def] using memLp_mul_bounded (memLp_gamma_lipschitz hfin hpar hu.1 hLip) hη2M hη2B
  have hφS := hu.1.comp_contDiff_lipschitz hfin hc hC h0
  refine ⟨hφS,hterm1.add hterm2,?_⟩
  intro v hv
  have hvη := hv.mul_bounded hfin hηS hηB hηG
  have hform := hu.2.2 (fun x => v x*(deriv φ ∘ u) x) hvη
  have hmul := gamma_mul_left hfin hpar hv.2.1 hηS hu.1.2.1 hηB hηG
  have hchain1 := gamma_comp_contDiff hfin hpar hu.1.2.1 hu.1.2.1 hd hηS.1 hη2B
  have hchain0 := gamma_comp_contDiff hfin hpar hu.1.2.1 hv.2.1 hc hφS.2.1.1 hηB
  have hi1 : Integrable (fun x => deriv φ (u x)*A x*v x) m := hterm1.integrable_mul hv.1
  have hi2 : Integrable (fun x => deriv (deriv φ) (u x)*gamma m u u x*v x) m := hterm2.integrable_mul hv.1
  have hi3 : Integrable (fun x => deriv φ (u x)*gamma m u v x) m :=
    (integrable_gamma hfin hu.1 hv).bdd_mul hη.continuous.aestronglyMeasurable hηB
  have he : (∫ x,gamma m u (fun y => v y*(deriv φ ∘ u) y) x ∂m) =
      (∫ x,deriv (deriv φ) (u x)*gamma m u u x*v x ∂m)+
      (∫ x,deriv φ (u x)*gamma m u v x ∂m) := by
    rw [← integral_add hi2 hi3]
    apply integral_congr_ae
    filter_upwards [hmul,hchain1,gamma_comm (m := m) u (fun y => v y*(deriv φ ∘ u) y),gamma_comm (m := m) v u] with x hm hc hc1 hc2
    rw [hc1,hm,hc,hc2]
    dsimp only [Function.comp_def]
    ring
  rw [he] at hform
  have heR : (∫ x,A x*(v x*(deriv φ ∘ u) x) ∂m) = ∫ x,deriv φ (u x)*A x*v x ∂m :=
    integral_congr_ae (ae_of_all _ fun x => by dsimp only [Function.comp_def]; ring)
  rw [heR] at hform
  have heL : (∫ x,gamma m (φ ∘ u) v x ∂m) = ∫ x,deriv φ (u x)*gamma m u v x ∂m := integral_congr_ae hchain0
  rw [heL]
  simp_rw [add_mul]
  rw [integral_add hi1 hi2]
  linarith
end WeakHessian

end
end InlinedFile120

end OAI
