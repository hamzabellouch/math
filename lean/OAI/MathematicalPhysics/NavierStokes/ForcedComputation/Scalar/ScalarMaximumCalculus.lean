import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput
import OAI.Analysis.AffineBernstein.LocalMaximumSecond

namespace OAI

/-! The local differential inequality behind scalar comparison. These
statements concern the actual first and second spatial derivatives. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set Filter
open scoped ContDiff Topology

theorem spatialD_neg (f : Plane → ℝ) (j : Fin 2) :
    spatialD j (fun x => -f x) = fun x => -spatialD j f x := by
  funext x
  simp only [spatialD, fderiv_fun_neg, neg_apply]

theorem scalarGenerator_neg (ν : ℝ) (a : Plane → Plane) (f : Plane → ℝ) (x : Plane) :
    scalarGenerator ν a (fun y => -f y) x = -scalarGenerator ν a f x := by
  simp only [scalarGenerator, scalarLaplacian, spatialD_neg, Finset.sum_neg_distrib,
    fderiv_fun_neg, neg_apply]
  ring

theorem spatialD_second_nonpos {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    {x : Plane} (hm : IsLocalMax f x) (j : Fin 2) :
    spatialD j (spatialD j f) x ≤ 0 := by
  let v := PlanarHamiltonian.basis j
  let γ : ℝ → Plane := fun t => x + t • v
  let g : ℝ → ℝ := fun t => f (γ t)
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa only [γ, one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgm : IsLocalMax g 0 := by
    have ht : Tendsto γ (𝓝 0) (𝓝 x) := by
      simpa only [γ, zero_smul, add_zero] using (hγ 0).continuousAt.tendsto
    change ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f (γ 0)
    simpa only [γ, zero_smul, add_zero] using ht.eventually hm
  have hd (t : ℝ) : deriv g t = spatialD j f (γ t) :=
    ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hp := ((spatialD_smooth j hf).differentiable (by simp) (γ 0)).hasFDerivAt
  have hs := (hp.comp_hasDerivAt 0 (hγ 0)).deriv
  have he : deriv (deriv g) 0 = spatialD j (spatialD j f) x := by
    rw [funext hd]
    simpa only [Function.comp_def, spatialD, γ, v, zero_smul, add_zero] using hs
  rw [← he]
  exact AffineBernstein.localMax_second_deriv_nonpos (hg.contDiffAt.of_le (by simp)) hgm

theorem scalarLaplacian_nonpos {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    {x : Plane} (hm : IsLocalMax f x) : scalarLaplacian f x ≤ 0 := by
  apply Finset.sum_nonpos
  intro j _
  exact spatialD_second_nonpos hf hm j

theorem scalarGenerator_nonpos {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    {x : Plane} (hm : IsLocalMax f x) {ν : ℝ} (hν : 0 ≤ ν) (a : Plane → Plane) :
    scalarGenerator ν a f x ≤ 0 := by
  unfold scalarGenerator
  rw [hm.fderiv_eq_zero]
  simp only [zero_apply, sub_zero]
  exact mul_nonpos_of_nonneg_of_nonpos hν (scalarLaplacian_nonpos hf hm)

end ForcedComputation.VelocityDetector

end

end OAI
