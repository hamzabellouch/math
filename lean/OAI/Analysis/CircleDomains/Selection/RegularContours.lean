import OAI.Analysis.CircleDomains.Sobolev.SmoothContours
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Connected.LocallyConnected

namespace OAI

/-!
# Smooth regular planar contours

The implicit function theorem supplies actual smooth local coordinates on a
regular scalar level. Compactness then makes the number of components finite.
For the subsequent circle-classification step, the needed classical result is
Milnor, *Topology from the Differentiable Viewpoint* (1965), Appendix
"Classifying 1-Manifolds", theorem on p. 55: a compact connected smooth
one-manifold without boundary is diffeomorphic to the circle. Primary scan:
https://www.ux1.eiu.edu/~cidelman/Classes/4855%20and%205220/Supplementary%20Texts/MilnorTopDiffVpt.pdf
-/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The kernel of a nonzero real scalar differential on the plane is a line. -/
theorem finrank_ker_planar_functional {L : ℂ →L[ℝ] ℝ} (hL : L ≠ 0) :
    Module.finrank ℝ L.ker = 1 := by
  have hlin : (L : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hL
    ext z
    exact congrArg (fun T : ℂ →ₗ[ℝ] ℝ => T z) h
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hlin
  rw [Complex.finrank_real_complex] at h
  change Module.finrank ℝ L.ker + 1 = 2 at h
  omega

/-- A genuine smooth ambient normal form for a regular planar scalar map.
The first chart coordinate is the original function, on its entire domain. -/
theorem exists_smooth_planar_level_chart {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ} (hz : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ (ℝ × ℝ), z ∈ e.source ∧
      (∀ w, (e w).1 = f w) ∧ ContDiff ℝ ∞ e ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  let L := fderiv ℝ f z
  have hL : L ≠ 0 := hz
  have hlin : (L : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hL
    ext w
    exact congrArg (fun T : ℂ →ₗ[ℝ] ℝ => T w) h
  have hsurj : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hlin
  have hd : HasStrictFDerivAt f L z := hf.contDiffAt.hasStrictFDerivAt (by simp)
  let p := hd.implicitFunctionDataOfComplemented f L hsurj
    L.ker_closedComplemented_of_finiteDimensional_range
  let k : L.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_ker_planar_functional hL, Module.finrank_self])
  let c : (ℝ × L.ker) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) k
  let g : ℂ → ℝ × ℝ := c ∘ p.prodFun
  have hp : ContDiff ℝ ∞ p.prodFun := by
    apply hf.prodMk
    exact (Classical.choose L.ker_closedComplemented_of_finiteDimensional_range).contDiff.comp
      (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ ∞ g := c.contDiff.comp hp
  let d : ℂ ≃L[ℝ] (ℝ × L.ker) :=
    p.leftDeriv.equivProdOfSurjectiveOfIsCompl p.rightDeriv
      p.range_leftDeriv p.range_rightDeriv p.isCompl_ker
  have hgd : HasFDerivAt g ((d.trans c : ℂ ≃L[ℝ] (ℝ × ℝ)) : ℂ →L[ℝ] (ℝ × ℝ)) z :=
    c.hasFDerivAt.comp z p.hasStrictFDerivAt.hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hgd (by simp)
  let S := {w | (fderiv ℝ g w).IsInvertible}
  have hS : IsOpen S :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage (hg.continuous_fderiv (by simp))
  have hzS : z ∈ S := by
    change (fderiv ℝ g z).IsInvertible
    rw [hgd.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  let e := e₀.restrOpen S hS
  have he : (e : ℂ → ℝ × ℝ) = g := rfl
  refine ⟨e, ⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hgd (by simp), hzS⟩,
    ?_, he ▸ hg, ?_⟩
  · intro w
    rfl
  · intro y hy
    obtain ⟨d', hd'⟩ := (e.map_target hy).2
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy (f₀' := d')
    · rw [he, hd']
      exact hg.differentiable (by simp) |>.differentiableAt.hasFDerivAt
    · rw [he]
      exact hg.contDiffAt

private noncomputable def levelChartInverse {f : ℂ → ℝ} {t : ℝ}
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (he : ∀ w, (e w).1 = f w) (z : {w // f w = t}) (y : ℝ) : {w // f w = t} := by
  classical
  exact if h : (t, y) ∈ e.target then
    ⟨e.symm (t, y), by
      rw [← he, e.right_inv h]⟩
  else z

private theorem levelChartInverse_coe {f : ℂ → ℝ} {t : ℝ}
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (he : ∀ w, (e w).1 = f w) (z : {w // f w = t})
    {y : ℝ} (hy : (t, y) ∈ e.target) :
    (levelChartInverse e he z y : ℂ) = e.symm (t, y) := by
  simp only [levelChartInverse, dite_eq_left hy]

/-- Restrict ambient regular-level coordinates to an actual real chart of the
level subtype. -/
noncomputable def planarLevelChart {f : ℂ → ℝ} {t : ℝ}
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (he : ∀ w, (e w).1 = f w) (z : {w // f w = t}) :
    OpenPartialHomeomorph {w // f w = t} ℝ where
  toFun w := (e w).2
  invFun := levelChartInverse e he z
  source := Subtype.val ⁻¹' e.source
  target := (fun y : ℝ => (t, y)) ⁻¹' e.target
  map_source' := by
    intro w hw
    change (t, (e w).2) ∈ e.target
    have hp : (t, (e w).2) = e w :=
      Prod.ext ((he w).trans w.property).symm rfl
    rw [hp]
    exact e.map_source hw
  map_target' := by
    intro y hy
    change (levelChartInverse e he z y : ℂ) ∈ e.source
    rw [levelChartInverse_coe e he z hy]
    exact e.map_target hy
  left_inv' := by
    intro w hw
    apply Subtype.ext
    have hw' : (t, (e w).2) ∈ e.target := by
      have hp : (t, (e w).2) = e w :=
        Prod.ext ((he w).trans w.property).symm rfl
      rw [hp]
      exact e.map_source hw
    rw [levelChartInverse_coe e he z hw']
    have hp : (t, (e w).2) = e w :=
      Prod.ext ((he w).trans w.property).symm rfl
    rw [hp, e.left_inv hw]
  right_inv' := by
    intro y hy
    rw [levelChartInverse_coe e he z hy, e.right_inv hy]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hw => hw)).snd
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_induced_rng.mpr
    have hc : ContinuousOn (fun y : ℝ => (levelChartInverse e he z y : ℂ))
        {y | (t, y) ∈ e.target} := by
      apply (e.continuousOn_symm.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => hy)).congr
      intro y hy
      exact levelChartInverse_coe e he z hy
    exact continuousOn_iff_continuous_domRestrict.mp hc

private theorem contDiffOn_planarLevelChart_transition {f : ℂ → ℝ} {t : ℝ}
    (e₁ e₂ : OpenPartialHomeomorph ℂ (ℝ × ℝ))
    (he₁ : ∀ w, (e₁ w).1 = f w) (he₂ : ∀ w, (e₂ w).1 = f w)
    (h₁ : ContDiffOn ℝ ∞ e₁.symm e₁.target) (h₂ : ContDiff ℝ ∞ e₂)
    (z₁ z₂ : {w // f w = t}) :
    ContDiffOn ℝ ∞ ((planarLevelChart e₁ he₁ z₁).symm.trans
      (planarLevelChart e₂ he₂ z₂))
      ((planarLevelChart e₁ he₁ z₁).symm.trans
        (planarLevelChart e₂ he₂ z₂)).source := by
  have hbase : ContDiffOn ℝ ∞ (fun y : ℝ => (e₂ (e₁.symm (t, y))).2)
      (planarLevelChart e₁ he₁ z₁).target := by
    exact (h₂.comp_contDiffOn (h₁.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => hy))).snd
  apply (hbase.mono inter_subset_left).congr
  intro y hy
  change (e₂ (levelChartInverse e₁ he₁ z₁ y)).2 = (e₂ (e₁.symm (t, y))).2
  rw [levelChartInverse_coe e₁ he₁ z₁ hy.1]

private noncomputable def regularLevelAmbient {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) (z : {w // f w = t}) :
    OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
  Classical.choose (exists_smooth_planar_level_chart hf (ht z z.property))

private theorem regularLevelAmbient_spec {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) (z : {w // f w = t}) :
    z.val ∈ (regularLevelAmbient hf ht z).source ∧
      (∀ w, (regularLevelAmbient hf ht z w).1 = f w) ∧
      ContDiff ℝ ∞ (regularLevelAmbient hf ht z) ∧
      ContDiffOn ℝ ∞ (regularLevelAmbient hf ht z).symm
        (regularLevelAmbient hf ht z).target :=
  Classical.choose_spec (exists_smooth_planar_level_chart hf (ht z z.property))

/-- The actual real atlas induced by implicit-function charts on a regular level. -/
@[instance_reducible]
noncomputable def regularLevelChartedSpace {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) :
    ChartedSpace ℝ {w // f w = t} where
  atlas := Set.range (fun z => planarLevelChart (regularLevelAmbient hf ht z)
    (regularLevelAmbient_spec hf ht z).2.1 z)
  chartAt z := planarLevelChart (regularLevelAmbient hf ht z)
    (regularLevelAmbient_spec hf ht z).2.1 z
  mem_chart_source z := (regularLevelAmbient_spec hf ht z).1
  chart_mem_atlas z := Set.mem_range_self z

/-- A regular level of a smooth planar scalar map is a smooth one-dimensional
manifold without boundary, with the topology inherited from the plane. -/
theorem regularLevel_isManifold {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) :
    letI := regularLevelChartedSpace hf ht
    IsManifold (𝓘(ℝ)) ∞ {w // f w = t} := by
  let := regularLevelChartedSpace hf ht
  apply isManifold_of_contDiffOn
  rintro e₁ e₂ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩
  simpa using contDiffOn_planarLevelChart_transition
    (regularLevelAmbient hf ht z₁) (regularLevelAmbient hf ht z₂)
    (regularLevelAmbient_spec hf ht z₁).2.1
    (regularLevelAmbient_spec hf ht z₂).2.1
    (regularLevelAmbient_spec hf ht z₁).2.2.2
    (regularLevelAmbient_spec hf ht z₂).2.2.1 z₁ z₂

/-- The manifold charts describe the existing planar inclusion; their smooth
structure is therefore compatible with the physical embedding. -/
theorem regularLevel_subtype_contMDiff {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) :
    letI := regularLevelChartedSpace hf ht
    ContMDiff (𝓘(ℝ)) (𝓘(ℝ, ℂ)) ∞ (Subtype.val : {w // f w = t} → ℂ) := by
  let := regularLevelChartedSpace hf ht
  intro z
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  let e := regularLevelAmbient hf ht z
  have he := (regularLevelAmbient_spec hf ht z).2.1
  let c := planarLevelChart e he z
  have hz : z ∈ c.source := (regularLevelAmbient_spec hf ht z).1
  have hy : (t, c z) ∈ e.target := c.map_source hz
  have hc : ContDiffAt ℝ ∞ (fun y : ℝ => e.symm (t, y)) (c z) :=
    ((regularLevelAmbient_spec hf ht z).2.2.2.contDiffAt (e.open_target.mem_nhds hy)).comp _
      (contDiffAt_const.prodMk contDiffAt_id)
  have heq : (fun y => (c.symm y : ℂ)) =ᶠ[𝓝 (c z)] (fun y => e.symm (t, y)) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hz)] with y hy
    exact levelChartInverse_coe e he z hy
  have hcinv := hc.congr_of_eventuallyEq heq
  have hchart : chartAt ℝ z = c := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq, hchart,
    Function.comp_def] using
    hcinv.contDiffWithinAt (s := (Set.univ : Set ℝ))

theorem regularLevel_locallyConnectedSpace {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t) :
    LocallyConnectedSpace {w // f w = t} := by
  let := regularLevelChartedSpace hf ht
  exact ChartedSpace.locallyConnectedSpace ℝ {w // f w = t}

/-- Compact regular planar levels have only finitely many connected components. -/
theorem finite_connectedComponents_regularLevel {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hc : IsCompact {w | f w = t}) :
    Finite (ConnectedComponents {w // f w = t}) := by
  let : CompactSpace {w // f w = t} := isCompact_iff_compactSpace.mp hc
  let := regularLevel_locallyConnectedSpace hf ht
  infer_instance

theorem finite_connectedComponents_nonzero_regularLevel {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    (ht : IsPlanarRegularValue f t) (ht0 : t ≠ 0) :
    Finite (ConnectedComponents {w // f w = t}) :=
  finite_connectedComponents_regularLevel hf ht
    (isCompact_nonzero_level hf.continuous hcompact ht0)

end CircleDomainRigidity

end OAI
