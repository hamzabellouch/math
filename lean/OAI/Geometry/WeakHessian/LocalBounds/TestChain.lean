import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.TestBochner
import OAI.Geometry.WeakHessian.Sobolev.LaplacianChain

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile121
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.test_comp_contDiff {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g : X → ℝ} (hg : IsTestFunction m g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) {C D E : ℝ≥0}
    (hC : LipschitzWith C φ) (hD : LipschitzWith D (deriv φ))
    (hE : LipschitzWith E (deriv (deriv φ))) (h0 : φ 0 = 0) :
    IsTestFunction m (φ ∘ g) := by
  obtain ⟨L,hL⟩ := hg.2.2.1
  obtain ⟨B,hB⟩ := hg.2.1
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hgen := (laplacian_isLaplacian hg.1).comp_contDiff hfin hpar hL (hφ.of_le (by norm_num)) hC hD h0
  have hsquare : Sobolev m (gamma m g g) :=
    (sobolev_congr_ae (gamma_self (m := m) g)).mpr (hrcd.test_gradientSquare_sobolev hN hfull hfin o hg)
  have hηB : ∀ᵐ x ∂m,|(deriv φ ∘ g) x| ≤ C := ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hC
  have hη2B : ∀ᵐ x ∂m,|(deriv (deriv φ) ∘ g) x| ≤ D := ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hD
  have gradbd {V : X → ℝ} {A : ℝ≥0} (hV : LipschitzWith A V) :
      ∀ᵐ x ∂m,|weakGradient m V x| ≤ A := by
    filter_upwards [weakGradient_nonneg (m := m) V,weakGradient_le_lipschitz hfin hV] with x hx hy
    simpa only [abs_of_nonneg hx] using hy
  have hs1 := hg.2.2.2.mul_bounded hfin (localSobolev_of_lipschitz hfin (hD.comp hL)) hηB (gradbd (hD.comp hL))
  have hs2 := hsquare.mul_bounded hfin (localSobolev_of_lipschitz hfin (hE.comp hL)) hη2B (gradbd (hE.comp hL))
  have hs : Sobolev m (fun x => deriv φ (g x)*laplacian m g x+deriv (deriv φ) (g x)*gamma m g g x) := by
    simpa only [Function.comp_def,mul_comm] using hs1.add hfin hs2
  refine ⟨⟨_,hgen⟩,⟨(C:ℝ)*B,fun x => ?_⟩,⟨C*L,hC.comp hL⟩,(sobolev_congr_ae (hgen.ae_laplacian hfin)).mpr hs⟩
  have HH := hC.dist_le_mul (g x) 0
  rw [h0,Real.dist_eq,sub_zero,Real.dist_eq,sub_zero] at HH
  exact HH.trans (mul_le_mul_of_nonneg_left (hB x) C.coe_nonneg)

lemma RCD.test_comp_contDiff_bounded_laplacian {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g : X → ℝ} (hg : IsTestFunction m g) {B : ℝ}
    (hB : ∀ᵐ x ∂m,|laplacian m g x| ≤ B)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) {C D E : ℝ≥0}
    (hC : LipschitzWith C φ) (hD : LipschitzWith D (deriv φ))
    (hE : LipschitzWith E (deriv (deriv φ))) (h0 : φ 0 = 0) :
    IsTestFunction m (φ ∘ g) ∧ ∃ A : ℝ,∀ᵐ x ∂m,|laplacian m (φ ∘ g) x| ≤ A := by
  refine ⟨hrcd.test_comp_contDiff hN hfull hfin o hg hφ hC hD hE h0,?_⟩
  obtain ⟨L,hL⟩ := hg.2.2.1
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hlap := ((laplacian_isLaplacian hg.1).comp_contDiff hfin hpar hL (hφ.of_le (by norm_num)) hC hD h0).ae_laplacian hfin
  refine ⟨(C:ℝ)*B+(D:ℝ)*(L:ℝ)^2,?_⟩
  filter_upwards [hlap,hB,gamma_self (m := m) g,weakGradient_nonneg (m := m) g,weakGradient_le_lipschitz hfin hL] with x hh hb hs hn hle
  rw [hh,hs]
  calc
    |deriv φ (g x)*laplacian m g x+deriv (deriv φ) (g x)*(weakGradient m g x)^2| ≤
        |deriv φ (g x)| *|laplacian m g x|+|deriv (deriv φ) (g x)| *(weakGradient m g x)^2 := by
      calc _ ≤ |deriv φ (g x)*laplacian m g x|+|deriv (deriv φ) (g x)*(weakGradient m g x)^2| := abs_add_le _ _
           _ = _ := by rw [abs_mul (deriv φ (g x)) (laplacian m g x),abs_mul (deriv (deriv φ) (g x)) ((weakGradient m g x)^2),abs_of_nonneg (sq_nonneg (weakGradient m g x))]
    _ ≤ (C:ℝ)*B+(D:ℝ)*(L:ℝ)^2 := add_le_add
      (mul_le_mul (norm_deriv_le_of_lipschitz hC) hb (abs_nonneg _) C.coe_nonneg)
      (mul_le_mul (norm_deriv_le_of_lipschitz hD) (pow_le_pow_left₀ hn hle 2) (sq_nonneg _) D.coe_nonneg)
end WeakHessian

end
end InlinedFile121

end OAI
