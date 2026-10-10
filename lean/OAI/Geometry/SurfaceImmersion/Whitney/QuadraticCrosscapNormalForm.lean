import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticCrosscapFactorization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! Actual smooth target coordinates identifying a prepared quadratic jet
with the standard Whitney umbrella. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance normalSourceNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance normalSourceSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

theorem quadratic_crosscap_normal_form {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    ∃ (S : Base ≃L[ℝ] Base) (e : OpenPartialHomeomorph (Base × ℝ) (ProjectionTarget 3)),
      0 ∈ e.source ∧ e 0 = f a ∧ ContDiff ℝ ∞ e ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x, centeredSurfaceTaylor f a (a+S x) = e (standardCrosscap x) := by
  obtain ⟨R,β,hfactor⟩ := quadratic_crosscap_factorization hf a b t hz hreg
  let g : Base × ℝ → ProjectionTarget 3 := fun z => f a + R (crosscapTargetShear β z)
  have hg : ContDiff ℝ ∞ g := contDiff_const.add (R.contDiff.comp (crosscapTargetShear_smooth β))
  have hd : HasFDerivAt g R.toContinuousLinearMap 0 := by
    have hs := ((crosscapTargetShear_smooth β).differentiable (by simp) 0).hasFDerivAt
    rw [crosscapTargetShear_fderiv] at hs
    convert ((R.hasFDerivAt.comp 0 hs).const_add (f a)) using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro z
      rfl
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd (by simp)
  let W : Set (Base × ℝ) := {z | IsUnit (R.symm.toContinuousLinearMap.comp (fderiv ℝ g z))}
  have hcont : Continuous (fun z => R.symm.toContinuousLinearMap.comp (fderiv ℝ g z)) :=
    continuous_const.clm_comp (hg.continuous_fderiv (by simp))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have h0W : (0 : Base × ℝ) ∈ W := by
    change IsUnit (R.symm.toContinuousLinearMap.comp (fderiv ℝ g 0))
    rw [hd.fderiv]
    have heq : R.symm.toContinuousLinearMap.comp R.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (Base × ℝ) := by
      apply ContinuousLinearMap.ext
      intro z
      exact R.symm_apply_apply z
    rw [heq]
    exact isUnit_one
  let e := e₀.restrOpen W hW
  have he : (e : Base × ℝ → ProjectionTarget 3) = g := rfl
  refine ⟨crosscapSourceEquiv b t,e,
    ⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),h0W⟩,?_,?_,?_,?_⟩
  · change f a+R (crosscapTargetShear β 0) = f a
    simp [crosscapTargetShear]
  · simpa only [he] using hg
  · intro y hy
    obtain ⟨u,hu⟩ := (e.map_target hy).2
    let D := (ContinuousLinearEquiv.ofUnit u).trans R
    have hD : D.toContinuousLinearMap = fderiv ℝ g (e.symm y) := by
      apply ContinuousLinearMap.ext
      intro z
      change R ((u : (Base × ℝ) →L[ℝ] (Base × ℝ)) z) = _
      rw [hu]
      exact R.apply_symm_apply _
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he,hD]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hg.contDiffAt)).contDiffWithinAt
  · exact hfactor

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
