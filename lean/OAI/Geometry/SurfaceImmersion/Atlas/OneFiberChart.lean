import OAI.Geometry.SurfaceImmersion.Geometry.OneFiberAugmentation

namespace OAI

/-! Smooth submersion coordinates with one-dimensional fibers. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem one_fiber_submersion_chart (hdimEF : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    {f : E → F}
    (hf : ContDiff ℝ ∞ f) (p : E)
    (hsurj : Function.Surjective (fderiv ℝ f p)) :
    ∃ e : OpenPartialHomeomorph E (F × ℝ), p ∈ e.source ∧
      (∀ x, (e x).1 = f x) ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨ℓ,hℓ⟩ := one_fiber_linear_augmentation hdimEF (fderiv ℝ f p) hsurj
  let L := ContinuousLinearEquiv.ofBijective ((fderiv ℝ f p).prod ℓ)
    (LinearMap.ker_eq_bot.mpr hℓ.1) (LinearMap.range_eq_top.mpr hℓ.2)
  let g : E → F × ℝ := fun x => (f x,ℓ x)
  have hg : ContDiff ℝ ∞ g := hf.prodMk ℓ.contDiff
  have hd : HasFDerivAt g L.toContinuousLinearMap p :=
    (hf.differentiable (by simp) p).hasFDerivAt.prodMk ℓ.hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd (by simp)
  let W : Set E := {x | IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g x))}
  have hcont : Continuous (fun x => L.symm.toContinuousLinearMap.comp (fderiv ℝ g x)) :=
    continuous_const.clm_comp (hg.continuous_fderiv (by simp))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have hpW : p ∈ W := by
    change IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g p))
    rw [hd.fderiv]
    have heq : L.symm.toContinuousLinearMap.comp L.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ E := by
      apply ContinuousLinearMap.ext
      intro v
      exact L.symm_apply_apply v
    rw [heq]
    exact isUnit_one
  let e := e₀.restrOpen W hW
  have he : (e : E → F × ℝ) = g := rfl
  refine ⟨e,⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),hpW⟩,
    (fun _ => rfl),?_,?_⟩
  · simpa only [he] using hg
  · intro y hy
    have hunit : IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g (e.symm y))) :=
      (e.map_target hy).2
    obtain ⟨u,hu⟩ := hunit
    let D := (ContinuousLinearEquiv.ofUnit u).trans L
    have heq : D.toContinuousLinearMap = fderiv ℝ g (e.symm y) := by
      apply ContinuousLinearMap.ext
      intro v
      change L ((u : E →L[ℝ] E) v) = _
      rw [hu]
      exact L.apply_symm_apply _
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he,heq]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hg.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
