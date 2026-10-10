import OAI.Analysis.CircleDomains.Selection.RegularContours

namespace OAI

/-! A local C1 normal form, retaining the actual first coordinate, on the
open domain of a scalar planar function. -/
open Set Filter Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_c1_planar_level_chart {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {z : ℂ} (hzD : z ∈ D)
    (hz : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ (ℝ × ℝ), z ∈ e.source ∧ e.source ⊆ D ∧
      (∀ w, (e w).1 = f w) ∧ ContDiffOn ℝ 1 e e.source ∧
      ContDiffOn ℝ 1 e.symm e.target := by
  let L := fderiv ℝ f z
  have hL : L ≠ 0 := hz
  have hlin : (L : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hL
    ext w
    exact congrArg (fun T : ℂ →ₗ[ℝ] ℝ => T w) h
  have hsurj : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hlin
  have hd : HasStrictFDerivAt f L z :=
    (hf.contDiffAt (hD.mem_nhds hzD)).hasStrictFDerivAt (by simp)
  let p := hd.implicitFunctionDataOfComplemented f L hsurj
    L.ker_closedComplemented_of_finiteDimensional_range
  let k : L.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_ker_planar_functional hL, Module.finrank_self])
  let c : (ℝ × L.ker) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) k
  let g : ℂ → ℝ × ℝ := c ∘ p.prodFun
  have hp : ContDiffOn ℝ 1 p.prodFun D := by
    apply hf.prodMk
    exact ((Classical.choose L.ker_closedComplemented_of_finiteDimensional_range).contDiff.comp
      (contDiff_id.sub contDiff_const)).contDiffOn
  have hg : ContDiffOn ℝ 1 g D := c.contDiff.comp_contDiffOn hp
  let d : ℂ ≃L[ℝ] (ℝ × L.ker) :=
    p.leftDeriv.equivProdOfSurjectiveOfIsCompl p.rightDeriv
      p.range_leftDeriv p.range_rightDeriv p.isCompl_ker
  have hgd : HasFDerivAt g ((d.trans c : ℂ ≃L[ℝ] (ℝ × ℝ)) : ℂ →L[ℝ] (ℝ × ℝ)) z :=
    c.hasFDerivAt.comp z p.hasStrictFDerivAt.hasFDerivAt
  have hgz := hg.contDiffAt (hD.mem_nhds hzD)
  let e₀ := hgz.toOpenPartialHomeomorph g hgd (by simp)
  have hinv : (fderiv ℝ g z).IsInvertible := by
    rw [hgd.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  have hN : {w | w ∈ D ∧ (fderiv ℝ g w).IsInvertible} ∈ 𝓝 z := by
    apply inter_mem (hD.mem_nhds hzD)
    exact (hgz.continuousAt_fderiv (by simp)).preimage_mem_nhds
      (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hinv)
  obtain ⟨U, hU, hUo, hzU⟩ := mem_nhds_iff.mp hN
  let e := e₀.restrOpen U hUo
  have he : (e : ℂ → ℝ × ℝ) = g := rfl
  have heD : e.source ⊆ D := fun w hw => (hU hw.2).1
  refine ⟨e, ⟨hgz.mem_toOpenPartialHomeomorph_source hgd (by simp), hzU⟩, heD,
    (fun _ => rfl), he ▸ hg.mono heD, ?_⟩
  intro y hy
  obtain ⟨d', hd'⟩ := (hU (e.map_target hy).2).2
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm hy (f₀' := d')
  · rw [he, hd']
    exact (hg.contDiffAt (hD.mem_nhds (heD (e.map_target hy)))).differentiableAt (by simp) |>.hasFDerivAt
  · rw [he]
    exact hg.contDiffAt (hD.mem_nhds (heD (e.map_target hy)))

end CircleDomainRigidity

end

end OAI
