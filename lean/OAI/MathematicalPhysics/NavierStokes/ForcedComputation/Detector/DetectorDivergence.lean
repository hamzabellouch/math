import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorStirring
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassCalculus

namespace OAI

/-! The explicitly scheduled detector drift is incompressible. Local finite
summation permits differentiation of the full schedule at every time. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Filter
open scoped ContDiff Topology BigOperators

theorem planar_divergence_trace {a : Plane → Plane} (ha : ContDiff ℝ ∞ a) (x : Plane) :
    PlanarHamiltonian.divergence a x =
      ∑ j : Fin 2, fderiv ℝ a x (PlanarHamiltonian.basis j) j := by
  apply Finset.sum_congr rfl
  intro j _
  unfold PlanarHamiltonian.spatialD
  rw [fderiv_apply (ha.differentiable (by simp) x) j]
  rfl

theorem planar_divergence_congr {a b : Plane → Plane}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) {x : Plane} (he : a =ᶠ[𝓝 x] b) :
    PlanarHamiltonian.divergence a x = PlanarHamiltonian.divergence b x := by
  rw [planar_divergence_trace ha, planar_divergence_trace hb, he.fderiv_eq]

theorem planar_divergence_sum (N : ℕ) (F : ℕ → Plane → Plane)
    (hF : ∀ n, ContDiff ℝ ∞ (F n)) (x : Plane) :
    PlanarHamiltonian.divergence (fun y => ∑ n ∈ Finset.range N, F n y) x =
      ∑ n ∈ Finset.range N, PlanarHamiltonian.divergence (F n) x := by
  rw [planar_divergence_trace (ContDiff.sum (fun n _ => hF n))]
  rw [fderiv_fun_sum (fun n _ => (hF n).differentiable (by simp) x)]
  simp only [sum_apply, Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  exact (planar_divergence_trace (hF n) x).symm

theorem detectorDriftTerm_divergence {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (C L n : ℕ) (t : ℝ) (x : Plane) :
    PlanarHamiltonian.divergence (fun y => detectorDriftTerm V C L n (t, y)) x = 0 := by
  have hs : ContDiff ℝ ∞ (V (detectorPhase C L n t)) :=
    hV.comp (contDiff_const.prodMk contDiff_id)
  have h := divergence_scalar_product hs
    (contDiff_const (c := detectorSpeed C L n t)) x
  simpa only [detectorDriftTerm, hdiv, mul_zero, fderiv_const_apply, zero_apply,
    add_zero] using h

theorem detectorDrift_divergence {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (C L : ℕ) (t : ℝ) (x : Plane) :
    PlanarHamiltonian.divergence (detectorDrift V C L t) x = 0 := by
  obtain ⟨N, hN⟩ := detectorBlockSum_local (detectorDriftTerm V C L)
    (detectorDriftTerm_before V C L) (t, x)
  have he : detectorDrift V C L t =ᶠ[𝓝 x]
      fun y => ∑ n ∈ Finset.range N, detectorDriftTerm V C L n (t, y) :=
    hN.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto x)
  have hF (n : ℕ) : ContDiff ℝ ∞ (fun y => detectorDriftTerm V C L n (t, y)) :=
    (detectorDriftTerm_smooth hV C L n).comp (contDiff_const.prodMk contDiff_id)
  have hdt : ContDiff ℝ ∞ (detectorDrift V C L t) :=
    (detectorDrift_smooth hV C L).comp (contDiff_const.prodMk contDiff_id)
  rw [planar_divergence_congr hdt
      (ContDiff.sum (fun n _ => hF n)) he, planar_divergence_sum N _ hF]
  exact Finset.sum_eq_zero (fun n _ => detectorDriftTerm_divergence hV hdiv C L n t x)

end ForcedComputation.VelocityDetector

end

end OAI
