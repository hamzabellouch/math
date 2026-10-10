import OAI.Geometry.RCD.Sobolev.EulerOrthogonality
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! # From weak Euler limits to the Euclidean rigidity contradiction -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ContDiff

noncomputable section
namespace RegularPointCoordinates

/-- The weak identity supplied by convergence of gradient pairings is
pointwise for the smooth Euclidean harmonic limit. -/
theorem euler_equation_of_test_integrals {n : ℕ} {S : ℝ} (w : Euclidean n → ℝ)
    (hw : ContDiffOn ℝ 2 w (ball 0 S)) (ell : Euclidean n →L[ℝ] ℝ) (k : ℝ)
    (htest : ∀ ψ : Euclidean n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball 0 S →
      (∫ x in ball 0 S, ψ x * (fderiv ℝ w x x - w x - ell x - k)) = 0) :
    ∀ x ∈ ball 0 S, fderiv ℝ w x x = w x + ell x + k := by
  let F := fun x => fderiv ℝ w x x - w x - ell x - k
  have hDsm : ContDiffOn ℝ 1 (fderiv ℝ w) (ball 0 S) :=
    hw.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hDF : ContinuousOn (fderiv ℝ w) (ball 0 S) := hDsm.continuousOn
  have hF : ContinuousOn F (ball 0 S) :=
    (((hDF.clm_apply continuousOn_id).sub hw.continuousOn).sub ell.continuous.continuousOn).sub
      continuousOn_const
  have hae : ∀ᵐ x ∂(volume : Measure (Euclidean n)), x ∈ ball 0 S → F x = 0 := by
    apply isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hF.locallyIntegrableOn measurableSet_ball)
    intro ψ hψ hs hsub
    have heq : (∫ x in ball 0 S, ψ x * F x) = ∫ x, ψ x * F x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)), zero_mul])
    change (∫ x, ψ x * F x) = 0
    rw [← heq]
    exact htest ψ hψ hs hsub
  have hae' : F =ᵐ[volume.restrict (ball 0 S)] fun _ => (0 : ℝ) :=
    (ae_restrict_iff' measurableSet_ball).2 hae
  have heq := Measure.eqOn_open_of_ae_eq hae' isOpen_ball hF continuousOn_const
  intro x hx
  have hh := heq hx
  dsimp only [F] at hh
  linarith only [hh]

/-- It is enough to pass the Euler equation against interior smooth
tests. The moment limits alone then contradict the positive norm. -/
theorem EuclideanHarmonicModel.no_unit_weak_euler_residual {n : ℕ} {S r : ℝ}
    (w : EuclideanHarmonicModel n S) (hS : 0 < S) (hr : r ≤ S)
    (ell : Euclidean n →L[ℝ] ℝ) (k : ℝ)
    (htest : ∀ ψ : Euclidean n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball 0 S →
      (∫ x in ball 0 S, ψ x * (fderiv ℝ w.value x x - w.value x - ell x - k)) = 0)
    (hunit : ⟪w.moments hr none, w.moments hr none⟫_ℝ = 1)
    (hone : ⟪w.moments hr none, w.moments hr (some none)⟫_ℝ = 0)
    (hcoords : ∀ i, ⟪w.moments hr none, w.moments hr (some (some i))⟫_ℝ = 0) : False :=
  w.no_unit_euler_residual hS hr ell k
    (euler_equation_of_test_integrals w.value w.harmonic.contDiffOn ell k htest) hunit hone hcoords

end RegularPointCoordinates

end

end OAI
