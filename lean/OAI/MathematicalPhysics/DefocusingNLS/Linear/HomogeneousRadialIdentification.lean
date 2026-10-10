import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialCompletion
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialWeakTesting
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalRadialTesting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! # Identification of the classical exterior radial derivative

Local smooth jets are identified with the completed radial L² derivative by
test functions. No smoothness through the origin or interface is required.
-/

open MeasureTheory Set Filter
open scoped SchwartzMap

namespace DefocusingNLS

private theorem compact_test_integrable (U : Set ℝ) (G : ℝ → ℂ)
    (hG : LocallyIntegrableOn G U) (ψ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun r => ψ r * G r) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left _ _).trans (subset_tsupport ψ))).mp
  exact IntegrableOn.continuousOn_mul ψ.continuous.continuousOn
    (hG.integrableOn_compact_subset hs hc) hc

/-- Local test equality suffices to identify a classical representative of
the completed radial function on an exterior interval. -/
theorem positiveRadiusExtension_eq_of_local_testing
    (g : PhysicalPositiveRadius → ℂ) (hg : MemLp g 2 physicalRadiusMeasure)
    (R : ℝ) (hR : 0 ≤ R) (F : ℝ → ℂ) (hF : ContinuousOn F (Ioi R))
    (htest : ∀ ψ : 𝓢(ℝ, ℂ), HasCompactSupport ψ → tsupport ψ ⊆ Ioi R →
      (∫ r, ψ r * ((r : ℂ) ^ (11 : ℕ) * positiveRadiusExtension g r)) =
        ∫ r, ψ r * ((r : ℂ) ^ (11 : ℕ) * F r)) :
    ∀ᵐ r ∂volume, r ∈ Ioi R → positiveRadiusExtension g r = F r := by
  let G : ℝ → ℂ := fun r => (r : ℂ) ^ (11 : ℕ) * positiveRadiusExtension g r
  let H : ℝ → ℂ := fun r => (r : ℂ) ^ (11 : ℕ) * F r
  have hG : LocallyIntegrableOn G (Ioi R) :=
    (positiveRadiusExtension_weighted_locallyIntegrable g hg).mono_set (Ioi_subset_Ioi hR)
  have hH : LocallyIntegrableOn H (Ioi R) :=
    ((Complex.continuous_ofReal.pow 11).continuousOn.mul hF).locallyIntegrableOn
      measurableSet_Ioi
  have heq := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hG.sub hH)
    (by
      intro φ hφ hc hs
      have hcc : HasCompactSupport (fun r => (φ r : ℂ)) :=
        hc.comp_left (g := Complex.ofReal) (by simp)
      let ψ : 𝓢(ℝ, ℂ) := hcc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ)
      have hψ : HasCompactSupport ψ := hcc
      have hsψ : tsupport ψ ⊆ Ioi R := by
        change closure (Function.support (fun r => (φ r : ℂ))) ⊆ Ioi R
        have he : Function.support (fun r => (φ r : ℂ)) = Function.support φ := by
          ext r
          simp
        rwa [he]
      have hiG := compact_test_integrable (Ioi R) G hG ψ hψ hsψ
      have hiH := compact_test_integrable (Ioi R) H hH ψ hψ hsψ
      calc
        (∫ r, φ r • (G r - H r)) = ∫ r, ψ r * G r - ψ r * H r := by
          apply integral_congr_ae
          filter_upwards [] with r
          change φ r • (G r - H r) = (φ r : ℂ) * G r - (φ r : ℂ) * H r
          rw [Complex.real_smul, mul_sub]
        _ = (∫ r, ψ r * G r) - ∫ r, ψ r * H r := integral_sub hiG hiH
        _ = 0 := sub_eq_zero.mpr (htest ψ hψ hsψ))
  filter_upwards [heq] with r hr hmem
  have hr0 : 0 < r := hR.trans_lt hmem
  have hz : (r : ℂ) ^ (11 : ℕ) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr0.ne')
  have hh := sub_eq_zero.mp (hr hmem)
  exact (mul_left_cancel₀ hz hh)

private theorem radialTransposedTest_eq (N : ℕ) (ψ : 𝓢(ℝ, ℂ)) (r : ℝ) :
    radialTransposedTest N ψ r = scalarSchwartzJet N (radialWeightedSchwartzTest ψ) r := by
  rw [scalarSchwartzJet_apply]
  exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv

/-- The classical Nth radial jet on a smooth exterior interval agrees almost
everywhere with the exact contraction of the completed Cartesian derivatives. -/
theorem homogeneousRadialAngularDerivative_eq_classical
    (a : ℝ) (N : ℕ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (u : HomogeneousY a N) (R : ℝ) (hR : 0 ≤ R) (F : ℕ → ℝ → ℂ)
    (hF : ∀ j r, r ∈ Ioi R → HasDerivAt (F j) (F (j + 1) r) r)
    (hF0 : F 0 = homogeneousAngularProjection a N ha ha1 hk h u) :
    ∀ᵐ r ∂volume, r ∈ Ioi R →
      positiveRadiusExtension (homogeneousRadialAngularDerivative a N ha ha1 hk h u) r =
        F N r := by
  apply positiveRadiusExtension_eq_of_local_testing _
    (homogeneousRadialAngularDerivative_memLp a N ha ha1 hk h hh u) R hR (F N)
    (fun r hr => (hF N r hr).continuousAt.continuousWithinAt)
  intro ψ hc hs
  have hψ : ∀ r, r ≤ 0 → ψ r = 0 := by
    intro r hr
    apply image_eq_zero_of_notMem_tsupport
    exact fun hm => (not_lt_of_ge (hr.trans hR)) (hs hm)
  have hweak := homogeneousAngularProjection_weak_derivative a N ha ha1 hk h hh ψ hψ u
  have hclass := local_radial_iterated_integration_by_parts (Ioi R) F hF N
    (radialWeightedSchwartzTest ψ)
    (hc.of_isClosed_subset isClosed_closure (tsupport_radialWeightedSchwartzTest_subset ψ))
    ((tsupport_radialWeightedSchwartzTest_subset ψ).trans hs)
  have hi : (∫ r, ψ r * ((r : ℂ) ^ (11 : ℕ) *
        positiveRadiusExtension (homogeneousRadialAngularDerivative a N ha ha1 hk h u) r)) =
      ∫ r, ψ r * homogeneousRadialAngularDerivative a N ha ha1 hk h u r
        ∂physicalRadiusMeasure := by
    rw [← integral_Ioi_eq_of_zero_nonpositive _
      (fun r hr => by simp [hψ r hr])]
    calc
      (∫ r in Ioi (0 : ℝ), ψ r * ((r : ℂ) ^ (11 : ℕ) *
          positiveRadiusExtension (homogeneousRadialAngularDerivative a N ha ha1 hk h u) r)) =
          ∫ r in Ioi (0 : ℝ), (r ^ (11 : ℕ) : ℝ) • (ψ r *
            positiveRadiusExtension (homogeneousRadialAngularDerivative a N ha ha1 hk h u) r) := by
        apply integral_congr_ae
        filter_upwards [] with r
        simp only [Complex.real_smul, Complex.ofReal_pow]
        ring
      _ = _ := by
        symm
        simpa only [positiveRadiusExtension_coe] using integral_physicalRadiusMeasure
          (fun r => ψ r * positiveRadiusExtension
            (homogeneousRadialAngularDerivative a N ha ha1 hk h u) r)
  rw [hi, hweak, ← hF0]
  simpa only [radialTransposedTest_eq, radialWeightedSchwartzTest_apply, mul_assoc,
    mul_left_comm (ψ _)] using hclass.symm

/-- The classical exterior Nth radial derivative has the weighted L²
integrability required to exclude a nonzero fast outgoing component. -/
theorem homogeneousRadial_classical_weighted_square
    (a : ℝ) (N : ℕ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (u : HomogeneousY a N) (R : ℝ) (hR : 0 ≤ R) (F : ℕ → ℝ → ℂ)
    (hF : ∀ j r, r ∈ Ioi R → HasDerivAt (F j) (F (j + 1) r) r)
    (hF0 : F 0 = homogeneousAngularProjection a N ha ha1 hk h u) :
    IntegrableOn (fun r : ℝ => r ^ (11 : ℕ) * ‖F N r‖ ^ 2) (Ioi R) :=
  positiveRadiusExtension_weighted_square_tail _
    (homogeneousRadialAngularDerivative_memLp a N ha ha1 hk h hh u) R hR (F N)
    (homogeneousRadialAngularDerivative_eq_classical a N ha ha1 hk h hh u R hR F hF hF0)

end DefocusingNLS

end OAI
