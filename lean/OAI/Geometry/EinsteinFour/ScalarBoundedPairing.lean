import OAI.Geometry.EinsteinFour.ScalarPoissonKernelContinuousEmbedding
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! Continuous test pairings for bounded representatives of local heat output. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalarBoundedTest_integrable (φ : 𝓢(V, ℂ)) (f : V →ᵇ ℂ) :
    Integrable (fun x => φ x * f x) :=
  φ.integrable.mul_bdd f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

def scalarBoundedTestPairing (φ : 𝓢(V, ℂ)) : (V →ᵇ ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, φ x * f x
      map_add' := by
        intro f g
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, mul_add]
        exact integral_add (scalarBoundedTest_integrable φ f) (scalarBoundedTest_integrable φ g)
      map_smul' := by
        intro c f
        simp only [BoundedContinuousFunction.coe_smul, mul_smul_comm,
          integral_smul, RingHom.id_apply] }
    (∫ x, ‖φ x‖) (by
      intro f
      calc
        ‖∫ x, φ x * f x‖ ≤ ∫ x, ‖φ x‖ * ‖f‖ := by
          apply norm_integral_le_of_norm_le (φ.integrable.norm.mul_const ‖f‖)
          exact Filter.Eventually.of_forall (fun x => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))
        _ = (∫ x, ‖φ x‖) * ‖f‖ := integral_mul_const _ _)

theorem scalarBoundedTestPairing_apply (φ : 𝓢(V, ℂ)) (f : V →ᵇ ℂ) :
    scalarBoundedTestPairing φ f = ∫ x, φ x * f x := rfl

theorem scalar_L2_eq_bounded_of_tests (u : Lp ℂ 2 (volume : Measure V)) (f : V →ᵇ ℂ)
    (h : ∀ φ : 𝓢(V, ℂ), (u : 𝓢'(V, ℂ)) φ = scalarBoundedTestPairing φ f) :
    (u : V → ℂ) =ᵐ[volume] f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num)) f.continuous.locallyIntegrable
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have he := h (hc'.toSchwartzMap hs')
  rw [Lp.toTemperedDistribution_apply, scalarBoundedTestPairing_apply] at he
  change (∫ x : V, (ψ x : ℂ) * u x) = ∫ x : V, (ψ x : ℂ) * f x at he
  simpa only [Complex.real_smul, smul_eq_mul] using he

end
end PositiveEinsteinFour.Geometry

end OAI
