import OAI.Analysis.Mahler.SphereVolumeOrientation
import OAI.Analysis.Mahler.SphereTransport
import OAI.Analysis.Mahler.FormStokes
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff
namespace Mahler

/-- Coordinates in the positively oriented orthonormal frame already used by sphereFlux. -/
def fluxCoordinates (k : ℕ) :
    (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean (k+1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((2*k+1)+1) => ℝ)).symm.trans
    (sphereFrame k).repr.symm.toContinuousLinearEquiv

lemma fluxCoordinates_basis (k : ℕ) (i : Fin ((2*k+1)+1)) :
    fluxCoordinates k (MahlerStokes.coordinateBasis ((2*k+1)+1) i) = sphereFrame k i := by
  apply (sphereFrame k).repr.injective
  simp [fluxCoordinates, MahlerStokes.coordinateBasis, OrthonormalBasis.repr_self]

lemma fluxCoordinates_repr (k : ℕ) (x : Fin ((2*k+1)+1) → ℝ) :
    (sphereFrame k).repr (fluxCoordinates k x) = WithLp.toLp 2 x := by
  simp [fluxCoordinates]

lemma norm_fluxCoordinates_sq (k : ℕ) (x : Fin ((2*k+1)+1) → ℝ) :
    ‖fluxCoordinates k x‖^2 = MahlerStokes.radiusSq x := by
  rw [MahlerStokes.radiusSq_eq_euclidean_norm_sq]
  exact congrArg (fun t : ℝ => t^2) ((sphereFrame k).repr.symm.norm_map _)

/-- Real-part projection on continuous forms, as a continuous linear map. -/
def realFormCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℕ) :
    (E [⋀^Fin q]→L[ℝ] ℂ) →L[ℝ] (E [⋀^Fin q]→L[ℝ] ℝ) :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℝ (Fin q) Complex.reCLM

@[simp] lemma realFormCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} (a : E [⋀^Fin q]→L[ℝ] ℂ) (v : Fin q → E) :
    realFormCLM E q a v = (a v).re := rfl

/-- Exterior differentiation commutes with taking the real part; C1 supplies
only the first derivative used here. -/
theorem extDeriv_realForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} {eta : E → E [⋀^Fin q]→L[ℝ] ℂ} {x : E}
    (h : DifferentiableAt ℝ eta x) :
    extDeriv (fun y => realFormCLM E q (eta y)) x =
      realFormCLM E (q+1) (extDeriv eta x) := by
  ext v
  change (ContinuousAlternatingMap.alternatizeUncurryFin
    (fderiv ℝ (fun y => realFormCLM E q (eta y)) x)) v =
      ((ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ eta x)) v).re
  have hd : fderiv ℝ (fun y => realFormCLM E q (eta y)) x =
      (realFormCLM E q).comp (fderiv ℝ eta x) := by
    simpa only [Function.comp_def] using ((realFormCLM E q).hasFDerivAt.comp x h.hasFDerivAt).fderiv
  rw [hd]
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.comp_apply, realFormCLM_apply]
  change _ = Complex.reCLM (∑ i : Fin (q+1), (-1 : ℤ)^i.val •
    fderiv ℝ eta x (v i) (i.removeNth v))
  simp only [map_sum, map_zsmul]
  rfl

/-- The actual real coordinate form, with the same ordered slots as eta. -/
def fluxPullback {k q : ℕ}
    (eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ)
    (x : Fin ((2*k+1)+1) → ℝ) :
    (Fin ((2*k+1)+1) → ℝ) [⋀^Fin q]→L[ℝ] ℝ :=
  realFormCLM _ q ((eta (fluxCoordinates k x)).compContinuousLinearMap
    (fluxCoordinates k).toContinuousLinearMap)

lemma contDiffOn_fluxPullback {k q : ℕ} {s : ℕ∞ω}
    {eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    {U : Set (ComplexEuclidean (k+1))} (h : ContDiffOn ℝ s eta U) :
    ContDiffOn ℝ s (fluxPullback eta) ((fluxCoordinates k) ⁻¹' U) := by
  exact (realFormCLM _ q).contDiff.comp_contDiffOn
    ((ContinuousAlternatingMap.compContinuousLinearMapCLM
      (fluxCoordinates k).toContinuousLinearMap).contDiff.comp_contDiffOn
      (h.comp (fluxCoordinates k).contDiff.contDiffOn (fun _ hx => hx)))

/-- Naturality for the actual fixed linear coordinates, requiring only a
first derivative of eta. The coordinate map itself is smooth. -/
theorem extDeriv_fluxPullback {k q : ℕ}
    {eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    {x : Fin ((2*k+1)+1) → ℝ} (h : DifferentiableAt ℝ eta (fluxCoordinates k x)) :
    extDeriv (fluxPullback eta) x = fluxPullback (extDeriv eta) x := by
  have hp : DifferentiableAt ℝ (fun y => (eta (fluxCoordinates k y)).compContinuousLinearMap
      (fluxCoordinates k).toContinuousLinearMap) x :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (fluxCoordinates k).toContinuousLinearMap (ι := Fin q) (F := ℂ)).differentiableAt.comp x
      (h.comp x (fluxCoordinates k).differentiableAt)
  change extDeriv (fun y => realFormCLM _ q
    ((eta (fluxCoordinates k y)).compContinuousLinearMap (fluxCoordinates k).toContinuousLinearMap)) x = _
  rw [extDeriv_realForm hp]
  have hn := extDeriv_pullback h ((fluxCoordinates k).contDiff.contDiffAt (n := 2)) (by simp)
  simpa only [ContinuousLinearEquiv.fderiv, fluxPullback] using congrArg (realFormCLM _ (q+1)) hn

end Mahler

end

end OAI
