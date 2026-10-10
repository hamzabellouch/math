import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialComplexTesting
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace OAI

/-! # Local radial integration by parts with a smooth test

Only derivatives on the support of the test are used. This is the local
classical side of the distributional identification; exterior solutions
need no artificial extension through the origin.
-/

open MeasureTheory Set
open scoped SchwartzMap

namespace DefocusingNLS

private theorem integrable_compactTest_mul (ψ : 𝓢(ℝ, ℂ))
    (hψ : HasCompactSupport ψ) (F : ℝ → ℂ)
    (hF : ∀ r ∈ tsupport ψ, ContinuousAt F r) :
    Integrable (fun r => ψ r * F r) := by
  have hc : Continuous (fun r => ψ r * F r) := by
    apply continuous_of_tsupport
    intro r hr
    exact ψ.continuous.continuousAt.mul (hF r (tsupport_mul_subset_left hr))
  exact hc.integrable_of_hasCompactSupport hψ.mul_right

noncomputable def scalarSchwartzJet (N : ℕ) (ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ)^[N] ψ

@[simp] theorem scalarSchwartzJet_apply (N : ℕ) (ψ : 𝓢(ℝ, ℂ)) (r : ℝ) :
    scalarSchwartzJet N ψ r = iteratedDeriv N ψ r := by
  induction N generalizing ψ with
  | zero => rfl
  | succ N ih =>
      rw [scalarSchwartzJet, Function.iterate_succ_apply]
      change scalarSchwartzJet N (SchwartzMap.derivCLM ℂ ℂ ψ) r = _
      rw [ih, iteratedDeriv_succ']
      rfl

/-- Classical local jets satisfy the full transposed identity against each
smooth compactly supported test in their domain. -/
theorem local_radial_iterated_integration_by_parts (U : Set ℝ)
    (F : ℕ → ℝ → ℂ)
    (hF : ∀ j r, r ∈ U → HasDerivAt (F j) (F (j + 1) r) r)
    (N : ℕ) (ψ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ r : ℝ, ψ r * F N r) =
      (-1 : ℂ) ^ N * ∫ r : ℝ, scalarSchwartzJet N ψ r * F 0 r := by
  induction N generalizing ψ with
  | zero => simp [scalarSchwartzJet]
  | succ N ih =>
      let ψ' := SchwartzMap.derivCLM ℂ ℂ ψ
      have hs' : tsupport ψ' ⊆ tsupport ψ := SchwartzMap.tsupport_derivCLM_subset ℂ ψ
      have hc' : HasCompactSupport ψ' := hc.of_isClosed_subset isClosed_closure hs'
      have hfirst : (∫ r : ℝ, ψ r * F (N + 1) r) =
          -(∫ r : ℝ, ψ' r * F N r) := by
        apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
          (L := ContinuousLinearMap.mul ℝ ℂ)
        · intro r _
          exact ψ.hasDerivAt r
        · intro r hr
          exact hF N r (hs hr)
        · exact integrable_compactTest_mul ψ hc (F (N + 1))
            (fun r hr => (hF (N + 1) r (hs hr)).continuousAt)
        · exact integrable_compactTest_mul ψ' hc' (F N)
            (fun r hr => (hF N r (hs (hs' hr))).continuousAt)
        · exact integrable_compactTest_mul ψ hc (F N)
            (fun r hr => (hF N r (hs hr)).continuousAt)
      rw [hfirst, ih ψ' hc' (hs'.trans hs)]
      have hj : scalarSchwartzJet N ψ' = scalarSchwartzJet (N + 1) ψ := by
        exact (Function.iterate_succ_apply (SchwartzMap.derivCLM ℂ ℂ) N ψ).symm
      rw [hj, pow_succ]
      ring

end DefocusingNLS

end OAI
