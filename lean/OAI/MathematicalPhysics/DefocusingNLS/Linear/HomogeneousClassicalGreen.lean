import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicTestCalculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace OAI

/-! # Compact-test Green identity for the actual C² physical realization

The physical function need not decay or have globally integrable derivatives:
every integrand is localized by the compactly supported smooth test.
-/

open MeasureTheory Set Filter Topology
open scoped SchwartzMap LineDeriv Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem continuous_laplacian_of_contDiff_two (F : E → ℂ) (hF : ContDiff ℝ 2 F) :
    Continuous (Δ F) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 12) ℝ)]
  exact continuous_finsetSum _ (fun j _ =>
    (hF.continuous_iteratedFDeriv (by norm_num)).eval_const
      ![(EuclideanSpace.basisFun (Fin 12) ℝ) j, (EuclideanSpace.basisFun (Fin 12) ℝ) j])

theorem hasCompactSupport_laplacian (F : E → ℂ) (hc : HasCompactSupport F) :
    HasCompactSupport (Δ F) := by
  apply hc.mono'
  intro x hx
  by_contra hnot
  have he : F =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hnot
  have hl := InnerProductSpace.laplacian_congr_nhds he
  have hz : Δ F x = 0 := by
    simpa only [InnerProductSpace.laplacian_const, Pi.zero_apply] using hl.eq_of_nhds
  exact hx hz

private theorem compactSchwartz_mul_continuous (ψ : 𝓢(E, ℂ))
    (hc : HasCompactSupport ψ) (F : E → ℂ) (hF : Continuous F) :
    Integrable (fun x => ψ x * F x) :=
  (ψ.continuous.mul hF).integrable_of_hasCompactSupport hc.mul_right

theorem compactTest_second_directional_green (ψ : 𝓢(E, ℂ))
    (hc : HasCompactSupport ψ) (F : E → ℂ) (hF : ContDiff ℝ 2 F) (v : E) :
    (∫ x : E, ψ x * iteratedFDeriv ℝ 2 F x ![v, v]) =
      ∫ x : E, iteratedFDeriv ℝ 2 ψ x ![v, v] * F x := by
  let ψ₁ : 𝓢(E, ℂ) := ∂_{v} ψ
  let ψ₂ : 𝓢(E, ℂ) := ∂_{v} ψ₁
  let F₁ : E → ℂ := fun x => fderiv ℝ F x v
  have hc₁ : HasCompactSupport ψ₁ := hc.of_isClosed_subset isClosed_closure
    (SchwartzMap.tsupport_lineDerivOp_subset v ψ)
  have hc₂ : HasCompactSupport ψ₂ := hc₁.of_isClosed_subset isClosed_closure
    (SchwartzMap.tsupport_lineDerivOp_subset v ψ₁)
  have hfd : ContDiff ℝ 1 (fderiv ℝ F) := (contDiff_succ_iff_fderiv.mp hF).2.2
  have hF₁ : ContDiff ℝ 1 F₁ := hfd.clm_apply contDiff_const
  have hF₂ : Continuous (fun x => fderiv ℝ F₁ x v) :=
    (contDiff_one_iff_fderiv.mp hF₁).2.clm_apply continuous_const
  have hψ₁ (x : E) : ψ₁ x = fderiv ℝ ψ x v :=
    SchwartzMap.lineDerivOp_apply_eq_fderiv v ψ x
  have hψ₂ (x : E) : ψ₂ x = fderiv ℝ ψ₁ x v :=
    SchwartzMap.lineDerivOp_apply_eq_fderiv v ψ₁ x
  have hfirst : (∫ x : E, ψ x * fderiv ℝ F₁ x v) =
      -(∫ x : E, ψ₁ x * F₁ x) := by
    simpa only [← hψ₁] using
      (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (f := fun x => ψ x) (g := F₁) (v := v)
        (by simpa only [← hψ₁] using compactSchwartz_mul_continuous ψ₁ hc₁ F₁ hF₁.continuous)
        (compactSchwartz_mul_continuous ψ hc _ hF₂)
        (compactSchwartz_mul_continuous ψ hc F₁ hF₁.continuous)
        (fun x _ => ψ.differentiableAt)
        (fun x _ => hF₁.differentiable one_ne_zero x))
  have hsecond : (∫ x : E, ψ₁ x * F₁ x) = -(∫ x : E, ψ₂ x * F x) := by
    simpa only [F₁, ← hψ₂] using
      (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (f := fun x => ψ₁ x) (g := F) (v := v)
        (by simpa only [← hψ₂] using compactSchwartz_mul_continuous ψ₂ hc₂ F hF.continuous)
        (compactSchwartz_mul_continuous ψ₁ hc₁ F₁ hF₁.continuous)
        (compactSchwartz_mul_continuous ψ₁ hc₁ F hF.continuous)
        (fun x _ => ψ₁.differentiableAt)
        (fun x _ => hF.differentiable (by norm_num) x))
  have hleft (x : E) : iteratedFDeriv ℝ 2 F x ![v, v] = fderiv ℝ F₁ x v :=
    radial_second_directional_eq F x v hF.contDiffAt
  have hright (x : E) : iteratedFDeriv ℝ 2 ψ x ![v, v] = ψ₂ x := by
    rw [radial_second_directional_eq ψ x v (ψ.smooth 2).contDiffAt, hψ₂]
    congr 2
  simp_rw [hleft, hright]
  rw [hfirst, hsecond, neg_neg]

/-- Green's identity against a compact smooth test, for a globally C²
physical function with no additional integrability hypothesis. -/
theorem compactTest_laplacian_green (ψ : 𝓢(E, ℂ))
    (hc : HasCompactSupport ψ) (F : E → ℂ) (hF : ContDiff ℝ 2 F) :
    (∫ x : E, ψ x * Δ F x) = ∫ x : E, Δ (fun y => ψ y) x * F x := by
  let e := EuclideanSpace.basisFun (Fin 12) ℝ
  have hli (j : Fin 12) : Integrable (fun x : E =>
      ψ x * iteratedFDeriv ℝ 2 F x ![e j, e j]) := by
    apply compactSchwartz_mul_continuous ψ hc
    exact (hF.continuous_iteratedFDeriv (by norm_num)).eval_const ![e j, e j]
  have hri (j : Fin 12) : Integrable (fun x : E =>
      iteratedFDeriv ℝ 2 ψ x ![e j, e j] * F x) := by
    let ψ₂ : 𝓢(E, ℂ) := ∂_{e j} (∂_{e j} ψ)
    have hc₁ : HasCompactSupport (∂_{e j} ψ : 𝓢(E, ℂ)) :=
      hc.of_isClosed_subset isClosed_closure (SchwartzMap.tsupport_lineDerivOp_subset (e j) ψ)
    have hc₂ : HasCompactSupport ψ₂ := hc₁.of_isClosed_subset isClosed_closure
      (SchwartzMap.tsupport_lineDerivOp_subset (e j) (∂_{e j} ψ))
    have heq (x : E) : iteratedFDeriv ℝ 2 ψ x ![e j, e j] = ψ₂ x := by
      exact (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
        (m := ![e j, e j]) (f := ψ) (x := x)).symm
    simp_rw [heq]
    exact compactSchwartz_mul_continuous ψ₂ hc₂ F hF.continuous
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e,
    Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => hli j), integral_finsetSum _ (fun j _ => hri j)]
  exact Finset.sum_congr rfl (fun j _ => compactTest_second_directional_green ψ hc F hF (e j))

end DefocusingNLS

end OAI
