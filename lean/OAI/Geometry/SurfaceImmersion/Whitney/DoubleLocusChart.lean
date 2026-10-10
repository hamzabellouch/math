import OAI.Geometry.SurfaceImmersion.Whitney.DoubleLocusAugmentation

namespace OAI

/-! Smooth submersion coordinates for the three-component difference
map on a pair of surface charts. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem double_locus_submersion_chart {f : Base × Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base × Base)
    (hsurj : Function.Surjective (fderiv ℝ f p)) :
    ∃ e : OpenPartialHomeomorph (Base × Base) (ProjectionTarget 3 × ℝ), p ∈ e.source ∧
      (∀ x, (e x).1 = f x) ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨ℓ,hℓ⟩ := double_locus_linear_augmentation (fderiv ℝ f p) hsurj
  let L := ContinuousLinearEquiv.ofBijective ((fderiv ℝ f p).prod ℓ)
    (LinearMap.ker_eq_bot.mpr hℓ.1) (LinearMap.range_eq_top.mpr hℓ.2)
  let g : Base × Base → ProjectionTarget 3 × ℝ := fun x => (f x,ℓ x)
  have hg : ContDiff ℝ ∞ g := hf.prodMk ℓ.contDiff
  have hd : HasFDerivAt g L.toContinuousLinearMap p :=
    (hf.differentiable (by simp) p).hasFDerivAt.prodMk ℓ.hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd (by simp)
  let W : Set (Base × Base) := {x | IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g x))}
  have hcont : Continuous (fun x => L.symm.toContinuousLinearMap.comp (fderiv ℝ g x)) :=
    continuous_const.clm_comp (hg.continuous_fderiv (by simp))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have hpW : p ∈ W := by
    change IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g p))
    rw [hd.fderiv]
    have heq : L.symm.toContinuousLinearMap.comp L.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (Base × Base) := by
      apply ContinuousLinearMap.ext
      intro v
      exact L.symm_apply_apply v
    rw [heq]
    exact isUnit_one
  let e := e₀.restrOpen W hW
  have he : (e : Base × Base → ProjectionTarget 3 × ℝ) = g := rfl
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
      change L ((u : (Base × Base) →L[ℝ] (Base × Base)) v) = _
      rw [hu]
      exact L.apply_symm_apply _
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he,heq]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hg.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
