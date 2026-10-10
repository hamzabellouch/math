import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationBarrierBounds

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma WeakLaplacianGE.add {f g q r : Position → ℝ} {U : Set Position}
    (hf : Continuous f) (hg : Continuous g)
    (hq : LocallyIntegrable q volume) (hr : LocallyIntegrable r volume)
    (hwf : WeakLaplacianGE f U q) (hwg : WeakLaplacianGE g U r) :
    WeakLaplacianGE (fun x => f x+g x) U (fun x => q x+r x) := by
  intro φ hφ hc ht hp
  have hL := (contDiff_coordinateLaplacian hφ).continuous
  have hLc := hasCompactSupport_coordinateLaplacian hc
  have hif := integrable_mul_compact_of_continuousAt (fun x _ => hf.continuousAt) hL hLc
  have hig := integrable_mul_compact_of_continuousAt (fun x _ => hg.continuousAt) hL hLc
  have hiq := integrable_mul_test_on (hq.locallyIntegrableOn U) hφ.continuous hc ht
  have hir := integrable_mul_test_on (hr.locallyIntegrableOn U) hφ.continuous hc ht
  simp_rw [add_mul]
  rw [integral_add hiq hir,integral_add hif hig]
  exact add_le_add (hwf φ hφ hc ht hp) (hwg φ hφ hc ht hp)

lemma WeakLaplacianGE.quadratic (a : ℝ) :
    WeakLaplacianGE (fun x : Position => a*‖x‖^2) univ (fun _ => 6*a) := by
  apply WeakLaplacianGE.of_classical
    (fun _ _ => (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt)
    (continuous_const.locallyIntegrable.locallyIntegrableOn univ)
  intro x hx
  simpa only [sub_zero] using (coordinateLaplacian_quadratic (0:Position) x a).ge

lemma WeakLaplacianGE.zero : WeakLaplacianGE (fun _ : Position => (0:ℝ)) univ (fun _ => 0) := by
  intro φ hφ hc ht hp
  simp

end NeutralAtom
end

end

end OAI
