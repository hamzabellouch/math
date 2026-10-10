import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseChart
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! A noncritical smooth phase is the first coordinate of a smooth local chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma phaseLinear_phaseDerivative (φ : Base → ℝ) (p : Base) :
    phaseLinear (phaseDerivative φ p) = fderiv ℝ φ p := by
  apply ContinuousLinearMap.ext
  intro v
  have he : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]
  conv_rhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,phaseLinear_apply,phaseDerivative]
  ring

/-- The chart is globally smooth as a function, and its inverse is smooth on
its target. Later cutoff extensions can make the inverse globally smooth. -/
theorem exists_smooth_phase_chart {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : Base} (hp : phaseDerivative φ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (∀ x, (e x).1 = φ x) ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let L := phaseEquiv (phaseDerivative φ p) hp
  let f : Base → Base := fun x => (φ x,(L x).2)
  have hf : ContDiff ℝ ∞ f := hφ.prodMk (contDiff_snd.comp L.contDiff)
  have hφ' : HasFDerivAt φ (phaseLinear (phaseDerivative φ p)) p := by
    rw [phaseLinear_phaseDerivative]
    exact (hφ.differentiable (by simp) p).hasFDerivAt
  have hf' : HasFDerivAt f L.toContinuousLinearMap p := by
    have hprod := hφ'.prodMk ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp p L.hasFDerivAt)
    have heq : (phaseLinear (phaseDerivative φ p)).prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap) = L.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [heq] at hprod
    exact hprod
  let e₀ := hf.contDiffAt.toOpenPartialHomeomorph f hf' (by simp)
  let W := {x : Base | IsUnit (fderiv ℝ f x)}
  have hW : IsOpen W := Units.isOpen.preimage (hf.continuous_fderiv (by simp))
  have hpW : p ∈ W := by
    change IsUnit (fderiv ℝ f p)
    rw [hf'.fderiv]
    exact L.toUnit.isUnit
  let e := e₀.restrOpen W hW
  have he : (e : Base → Base) = f := rfl
  refine ⟨e,?_,?_,?_,?_⟩
  · exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hf' (by simp),hpW⟩
  · exact fun x => rfl
  · simpa only [he] using hf
  · intro y hy
    have hunit : IsUnit (fderiv ℝ f (e.symm y)) := (e.map_target hy).2
    obtain ⟨u,hu⟩ := hunit
    let D := ContinuousLinearEquiv.ofUnit u
    have hd : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he]
      convert (hf.differentiable (by simp) (e.symm y)).hasFDerivAt using 1
      exact hu
    exact (e.contDiffAt_symm hy hd (by rw [he]; exact hf.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
